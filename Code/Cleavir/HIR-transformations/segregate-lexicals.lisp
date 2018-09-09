(cl:in-package #:cleavir-hir-transformations)

(defun data (instruction)
  (append (cleavir-ir:inputs instruction)
	  (cleavir-ir:outputs instruction)))

;;; By SEGREGATING lexical locations, we mean taking each lexical
;;; location and turning it into either a dynamic lexical location
;;; (which can be allocated in a register or on the stack) or a
;;; static lexical location (which may or may not be possible to
;;; allocate on the stack, and might have to be allocated in some
;;; other place, possibly on the heap).
;;;
;;; The method used here is very simple, and not particularly
;;; sophisticated.  It assumes that every nested function can escape
;;; in arbitrary ways, so that every lexical location that is shared
;;; by some function F and some other function G nested inside F must
;;; be an static lexical location.
;;;
;;; LOCATION-OWNERS is an EQ hash table mapping each lexical location
;;; to its owner.
;;;
;;; We return a list of the lexical locations that have been
;;; categorized as static lexical locations.

(defparameter *segregate-lexicals-meter*
  (make-instance 'cleavir-meter:size-meter
    :name "SEGREGATE-LEXICALS-METER"))

(defun segregate-lexicals (initial-instruction location-owners)
  (cleavir-meter:with-meter (m *segregate-lexicals-meter*)
    (let ((result '()))
      (cleavir-ir:map-instructions-with-owner
       (lambda (instruction owner)
	 (cleavir-meter:increment-size m)
	 (loop for datum in (data instruction)
	       do (when (typep datum 'cleavir-ir:lexical-location)
		    (unless (eq owner (gethash datum location-owners))
                      (pushnew datum result)))))
       initial-instruction)
      result)))

;;; Given a static lexical location and an EQ hash table giving the
;;; owner of each instruction, return a list of all the functions
;;; (represented by ENTER-INSTRUCTIONs) that use (read or write) the
;;; lexical location, i.e., a list of the owners of all instructions
;;; that use the lexical location.
;;;
;;; We are calling the two function CLEAVIR-IR:DEFINING-INSTRUCTIONS
;;; and CLEAVIR-IR:USING-INSTRUCTIONS, so this information must be up
;;; to date.
(defun functions-using-location (location instruction-owners)
  (let ((instructions (append (cleavir-ir:defining-instructions location)
			      (cleavir-ir:using-instructions location)))
	(result '()))
    (loop for instruction in instructions
	  do (pushnew (gethash instruction instruction-owners) result
		      :test #'eq))
    result))

;;; Given a list of ENTER-INSTRUCTIONs, return an alist mapping each
;;; ENTER-INSTRUCTION to a new dynamic lexical location for the
;;; purpose of holding a CELL associated with a static lexical
;;; location to be eliminated.
(defun allocate-cell-locations (enter-instructions)
  (loop for enter-instruction in enter-instructions
	collect (cons enter-instruction
                      (cleavir-ir:new-temporary "CELL"))))

;;; Given an ENCLOSE-INSTRUCTION and  the dynamic lexical location
;;; holding a cell in the function defined by the owner of the
;;; ENCLOSE-INSTRUCTION (IMPORT), import the cell to the ENCLOSE-INSTRUCTION.
;;;
;;; We add the import to the end of the import list in order to
;;; preserve the index of cells in the static environment.
(defun transmit-cell (enclose import)
  (let ((imports (cleavir-ir:inputs enclose)))
    ;; Start by adding the new import to the end of the existing
    ;; imports of the ENCLOSE-INSTRUCTION.
    (setf (cleavir-ir:inputs enclose) (append imports (list import)))))

;;; Add a fetch instruction after ENTER so that the cell is accessible.
(defun add-fetch (enter dloc)
  ;; Finally, add a new FETCH-INSTRUCTION after ENTER.
  (let ((env-location (cleavir-ir:static-environment enter))
        ;; The dynamic lexical variable that holds the static
	;; environment is the first output of the enter instruction.
	(cleavir-ir:*policy* (cleavir-ir:policy enter))
        ;; the index of the new cell in the closure will just be the
        ;; size of the existing closure vector.
        (new-index (cleavir-ir:closure-size enter)))
    (cleavir-ir:insert-instruction-after
     (cleavir-ir:make-fetch-instruction
      env-location
      (cleavir-ir:make-immediate-input new-index)
      dloc)
     enter)
    ;; Make sure we keep track of the closure vector expansion.
    (setf (cleavir-ir:closure-size enter) (1+ new-index))))

(defun dominating-instruction (basic-block defining-instructions)
  (cleavir-basic-blocks:map-basic-block-instructions
   (lambda (instruction)
     (when (member instruction defining-instructions)
       (return-from dominating-instruction instruction)))
   basic-block))

;;; The cell must be created when the variable comes into scope. In
;;; flow graph terms, this means at the instruction defining the
;;; variable closest to the root of the dominance tree in the owning
;;; function. ENCLOSE instructions whose CODE defines the variable
;;; also count as defining instructions.
(defun insert-create-cell-instruction
    (function-dag defining-instructions owner cell-locations instruction-basic-blocks dominance-tree)
  ;; Add the enclose instructions which define the variable to the set
  ;; of defining instructions.
  (let ((dag-nodes (dag-nodes function-dag)))
    (loop for (enter . cell-location) in cell-locations
          unless (eq enter owner)
            do (dolist (node (gethash enter dag-nodes))
                 (push (enclose-instruction node) defining-instructions))))
  (let* ((defining-blocks
           (remove-duplicates
            (remove-if-not (lambda (basic-block)
                             (eq (cleavir-basic-blocks:owner basic-block)
                                 owner))
                           (mapcar (lambda (instruction)
                                     (gethash instruction instruction-basic-blocks))
                                   defining-instructions))
            :test #'eq))
         (dominating-block (first defining-blocks))
         (dominating-block-distance (length (cleavir-dominance:dominators dominance-tree dominating-block))))
    (dolist (defining-block (rest defining-blocks))
      (let ((defining-block-distance (length (cleavir-dominance:dominators dominance-tree defining-block))))
        (when (< defining-block-distance dominating-block-distance)
          (setf dominating-block defining-block)
          (setf dominating-block-distance defining-block-distance))))
    ;; Start by creating a CREATE-CELL-INSTRUCTION in the basic block
    ;; before where the first definition of the variable appears.
    (let* ((first-instruction (dominating-instruction dominating-block defining-instructions))
           (cleavir-ir:*policy* (cleavir-ir:policy first-instruction)))
      (if (typep first-instruction 'cleavir-ir:enter-instruction)
          (cleavir-ir:insert-instruction-after
           (cleavir-ir:make-create-cell-instruction (cdr (assoc owner cell-locations)))
           first-instruction)
          (cleavir-ir:insert-instruction-before
           (cleavir-ir:make-create-cell-instruction (cdr (assoc owner cell-locations)))
           first-instruction)))))

;;; For a single static lexical location to be eliminated, make sure
;;; that the corresponding cell is available in all functions in which
;;; the static location is either read or written, as well as in the
;;; intermediate functions that neither read nor write the static
;;; location, but that occur between such a function and the owner of
;;; the static lexical location.  FUNCTION-DAG is a function dag
;;; defining the nesting of functions.  CELL-LOCATIONS is an alist
;;; mapping an ENTER-INSTRUCTION to the dynamic lexical location that
;;; holds the cell for the static lexical location in the function
;;; represented by that ENTER-INSTRUCTION.  ENTER-INSTRUCTIONs of
;;; intermediate functions are also present in CELL-LOCATIONS.  OWNER
;;; is the ENTER-INSTRUCTION that is the owner of the static lexical
;;; location to be eliminated.
;;;
;;; We proceed as follows: We insert new instructions after each
;;; ENTER-INSTRUCTION to write the cell into the dynamic lexical
;;; variable supplied for that purpose.  In OWNER's procedure, we
;;; insert a CREATE-CELL instruction after its first dominating
;;; definition.  For every other ENTER-INSTRUCTION in CELL-LOCATIONS
;;; we add a FETCH instruction after it, and we import the cell
;;; location of the parent function into the corresponding
;;; ENCLOSE-INSTRUCTION.
(defun ensure-cell-available (function-dag cell-locations owner)
  ;; For each entry in CELL-LOCATIONS other than OWNER, transmit
  ;; the cell from the corresponding ENCLOSE-INSTRUCTION to the
  ;; ENTER-INSTRUCTION of that entry.
  (loop with dag-nodes = (dag-nodes function-dag)
	for (enter . cell-location) in cell-locations
	unless (eq enter owner)
	  do (loop for node in (gethash enter dag-nodes)
                   for enclose = (enclose-instruction node)
                   for parents = (parents node)
                   do (loop for parent in parents
                            for parent-enter = (enter-instruction parent)
                            for import = (cdr (assoc parent-enter cell-locations))
                            do (transmit-cell enclose import)))
             (add-fetch enter cell-location)))

;;; Given a list of ENTER-INSTRUCTIONs representing the functions that
;;; read or write some particular static lexical location to
;;; eliminate, return a another list of ENTER-INSTRUCTIONs which is
;;; like the one passed as an argument, except that ENTER-INSTRUCTIONs
;;; representing intermediate functions have been added.  An
;;; intermediate function is one that neither reads nor writes the
;;; location, but that has an ancestor and a descendant that both do.
;;; FUNCTION-DAG is a function dag representing all the functions of
;;; the program.  OWNER is the ENTER-INSTRUCTION of the outermost
;;; function in the program that reads or writes the location.
(defun add-intermediate-functions (enter-instructions function-dag owner)
  (loop with todo = (loop for enter in enter-instructions
                          appending (gethash enter (dag-nodes function-dag)))
        with result = nil
        until (null todo)
        do (let* ((node (pop todo))
                  (enter (enter-instruction node)))
             (pushnew enter result :test #'eq)
             #+(or)
             (format t "Node: ~a~% Parents: ~a~%"
                     node (parents node))
             (unless (eq enter owner)
               (setf todo (append todo (parents node)))))
        finally (return result)))

;;; Given a single static lexical location SLOC, a dynamic lexical
;;; location CLOC holding the cell that replaces SLOC, and a single
;;; instruction INSTRUCTION that reads that location, create a new
;;; temporary dynamic lexical location D to hold the value of CLOC,
;;; insert a new READ-CELL instruction before INSTRUCTION that puts
;;; the contents of CLOC in SLOC, and replace all occurrences of SLOC
;;; in the inputs of I by D.
(defun replace-inputs (sloc cloc instruction)
  (let ((d (cleavir-ir:new-temporary))
	(cleavir-ir:*policy* (cleavir-ir:policy instruction)))
    (cleavir-ir:insert-instruction-before
     (cleavir-ir:make-read-cell-instruction cloc d)
     instruction)
    (cleavir-ir:substitute-input d sloc instruction)))

;;; Given a single static lexical location SLOC, a dynamic lexical
;;; location CLOC holding the cell that replaces SLOC, and a single
;;; instruction INSTRUCTION that writes that location, create a new
;;; temporary dynamic lexical location D to hold the value of CLOC,
;;; replace all occurrences of SLOC in the outputs of I by D, and
;;; insert a new WRITE-CELL instruction after INSTRUCTION that puts
;;; the value of D in CLOC.
(defun replace-outputs (sloc cloc instruction)
  (let ((d (cleavir-ir:new-temporary))
	(cleavir-ir:*policy* (cleavir-ir:policy instruction)))
    (cleavir-ir:substitute-output d sloc instruction)
    ;; CATCH has two successors and one output. There are other instructions
    ;; like that, but CATCH is the only one whose output is closed over in
    ;; normal code. Due to its unusual control flow, we special case it here.
    (if (typep instruction 'cleavir-ir:catch-instruction)
        (cleavir-ir:insert-instruction-between
         (cleavir-ir:make-write-cell-instruction cloc d)
         instruction
         (first (cleavir-ir:successors instruction)))
        (cleavir-ir:insert-instruction-after
         (cleavir-ir:make-write-cell-instruction cloc d)
         instruction))))

;;; Given a single static lexical location LOCATION, eliminate it by
;;; replacing all accesses to it by accesses to a corresponding CELL.
;;; FUNCTION-DAG is the function dag of the entire program.
;;; INSTRUCTION-OWNERS is a hash table mapping an instruction to its
;;; owner.  OWNER is the owner of LOCATION.
(defun process-location
    (location function-dag instruction-owners owner instruction-basic-blocks dominance-tree)
  (let* (;; Determine all the functions (represented by
	 ;; ENTER-INSTRUCTIONs) that use (read or write) the location.
	 (users (functions-using-location location instruction-owners))
	 ;; To that set, add the intermediate functions.
	 (enters (add-intermediate-functions users function-dag owner))
	 ;; Compute a dictionary that associates each
	 ;; ENTER-INSTRUCTION with a cell location.
	 (cell-locations (allocate-cell-locations enters))
         (defining-instructions (cleavir-ir:defining-instructions location)))
    (loop for instruction in (cleavir-ir:using-instructions location)
	  for instruction-owner = (gethash instruction instruction-owners)
	  for cell-location = (cdr (assoc instruction-owner cell-locations))
	  do (replace-inputs location cell-location instruction))
    (loop for instruction in defining-instructions
	  for instruction-owner = (gethash instruction instruction-owners)
	  for cell-location = (cdr (assoc instruction-owner cell-locations))
	  do (replace-outputs location cell-location instruction))
    (insert-create-cell-instruction function-dag
                                    defining-instructions
                                    owner cell-locations
                                    instruction-basic-blocks
                                    dominance-tree)
    ;; We do this step last, so that we are sure that the FETCH instructions are inserted immediately after the ENTER
    ;; instruction.
    (ensure-cell-available function-dag cell-locations owner)))

(defun process-captured-variables (initial-instruction)
  ;; Make sure everything is up to date.
  (cleavir-ir:reinitialize-data initial-instruction)
  (let* ((instruction-owners (compute-instruction-owners initial-instruction))
	 (location-owners (compute-location-owners initial-instruction))
	 (function-dag (build-function-dag initial-instruction))
	 (static-locations
	   (segregate-lexicals initial-instruction location-owners))
         (basic-blocks (cleavir-basic-blocks:basic-blocks initial-instruction))
         (instruction-basic-blocks (cleavir-basic-blocks:instruction-basic-blocks basic-blocks))
         (dominance-trees (make-hash-table :test #'eq)))
    (loop for static-location in static-locations
	  for owner = (gethash static-location location-owners)
	  do (process-location static-location
			       function-dag
			       instruction-owners
			       owner
                               instruction-basic-blocks
                               (alexandria:ensure-gethash
                                owner
                                dominance-trees
                                (cleavir-dominance:dominance-tree
                                 (find owner basic-blocks
                                       :key #'cleavir-basic-blocks:first-instruction)
                                 #'cleavir-basic-blocks:successors))))))

(defun segregate-only (initial-instruction)
  ;; Make sure everything is up to date.
  (cleavir-ir:reinitialize-data initial-instruction)
  (let ((location-owners (compute-location-owners initial-instruction)))
    (segregate-lexicals initial-instruction location-owners)))
