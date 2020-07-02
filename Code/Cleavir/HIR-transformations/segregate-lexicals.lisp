(cl:in-package #:cleavir-hir-transformations)

;;; FIXME: All comments out of date.

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
;;; ENTER-INSTRUCTION to a new dynamic lexical location.
(defun allocate-dynamic-locations (enter-instructions variable value-cell-p)
  (declare (ignore value-cell-p))
  (let ((name (cleavir-ir:name variable)))
    (loop for enter-instruction in enter-instructions
          collect (cons enter-instruction
                        (cleavir-ir:new-temporary
                         (if (symbolp name)
                             (symbol-name name)
                             "complex-name"))))))

;;; Given an ENCLOSE-INSTRUCTION and the dynamic lexical location ,
;;; import the dynamic lexical location to the ENCLOSE-INSTRUCTION
;;; (IMPORT).
;;;
;;; We add the import to the end of the import list in order to
;;; preserve the index of cells in the static environment.
(defun transmit-dynamic-location (enclose import instruction-owners)
  (let ((initializer (cleavir-ir:initializer enclose)))
    (unless initializer
      (let ((cleavir-ir:*origin* (cleavir-ir:origin enclose))
            (cleavir-ir:*policy* (cleavir-ir:policy enclose))
            (cleavir-ir:*dynamic-environment*
              (cleavir-ir:dynamic-environment enclose)))
        (setf initializer
              (cleavir-ir:make-initialize-closure-instruction
               (first (cleavir-ir:outputs enclose))
               nil)))
      ;; Defer initialization until all potentially mutually recurisve
      ;; functions are available.
      (do* ((instruction enclose successor)
            (successor (first (cleavir-ir:successors instruction)) (first (cleavir-ir:successors successor))))
           ((or (rest (cleavir-ir:predecessors successor))
                ;; This set of instruction types is guaranteed not to
                ;; call potentially uninitialized closures.
                (typecase successor
                  (cleavir-ir:enclose-instruction nil)
                  ((or cleavir-ir:assignment-instruction
                       cleavir-ir:lexical-bind-instruction)
                   (not (typep (first (cleavir-ir:defining-instructions
                                          (first (cleavir-ir:inputs successor))))
                               'cleavir-ir:enclose-instruction)))
                  (t t)))
            (cleavir-ir:insert-instruction-after initializer instruction)))
      (setf (cleavir-ir:initializer enclose) initializer)
      (setf (gethash initializer instruction-owners)
            (gethash enclose instruction-owners)))
    ;; Start by adding the new import to the end of the existing
    ;; imports of the INITIALIZE-CLOSURE-INSTRUCTION.
    (let ((imports (cleavir-ir:inputs initializer)))
      (setf (cleavir-ir:inputs initializer)
            (append imports (list import))))))

;;; Add a fetch instruction after ENTER so that the dynamic-location is accessible.
(defun add-fetch (enter dloc)
  ;; Finally, add a new FETCH-INSTRUCTION after ENTER.
  (let ((env-location (cleavir-ir:static-environment enter))
        (cleavir-ir:*origin* (cleavir-ir:origin enter))
	(cleavir-ir:*policy* (cleavir-ir:policy enter))
        (cleavir-ir:*dynamic-environment*
          (cleavir-ir:dynamic-environment enter))
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

;;; For a single static lexical location to be eliminated, make sure
;;; that the corresponding dynamic location, be it a cell or not, is
;;; available in all functions in which the static location is either
;;; read or written, as well as in the intermediate functions that
;;; neither read nor write the static location, but that occur between
;;; such a function and the owner of the static lexical location.
;;; FUNCTION-DAG is a function dag defining the nesting of functions.
;;; DYNAMIC-LOCATIONS is an alist mapping an ENTER-INSTRUCTION to the
;;; dynamic lexical location that holds the cell for the static
;;; lexical location in the function represented by that
;;; ENTER-INSTRUCTION.  ENTER-INSTRUCTIONs of intermediate functions
;;; are also present in DYNAMIC-LOCATIONS.  OWNER is the
;;; ENTER-INSTRUCTION that is the owner of the static lexical location
;;; to be eliminated.
;;;
;;; We proceed as follows: If the dynamic lexical locations are cells,
;;; we insert new instructions after each ENTER-INSTRUCTION to write
;;; the cell into the dynamic lexical variable supplied for that
;;; purpose.  After OWNER, we insert a CREATE-CELL instruction.  For
;;; every other ENTER-INSTRUCTION in DYNAMIC-LOCATIONS we add a FETCH
;;; instruction after it, and we import the dynamic location of the
;;; parent function into the corresponding ENCLOSE-INSTRUCTION.
(defun ensure-dynamic-location-available (function-dag dynamic-locations owner instruction-owners)
  ;; Next, for each entry in DYNAMIC-LOCATIONS other than OWNER, transmit
  ;; the cell from the corresponding ENCLOSE-INSTRUCTION to the
  ;; ENTER-INSTRUCTION of that entry.
  (loop with dag-nodes = (dag-nodes function-dag)
	for (enter . dynamic-location) in dynamic-locations
	unless (eq enter owner)
	  do (loop for node in (gethash enter dag-nodes)
                   for enclose = (enclose-instruction node)
                   for parents = (parents node)
                   do (loop for parent in parents
                            for parent-enter = (enter-instruction parent)
                            for import = (cdr (assoc parent-enter dynamic-locations))
                            do (transmit-dynamic-location enclose import instruction-owners)))
             (add-fetch enter dynamic-location)))

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
        (cleavir-ir:*origin* (cleavir-ir:origin instruction))
	(cleavir-ir:*policy* (cleavir-ir:policy instruction))
        (cleavir-ir:*dynamic-environment*
          (cleavir-ir:dynamic-environment instruction)))
    (cleavir-ir:insert-instruction-before
     (cleavir-ir:make-read-cell-instruction cloc d)
     instruction)
    (cleavir-ir:substitute-input d sloc instruction)
    #+nil
    (cleavir-hir-transformations:copy-propagate-1 d)))

;;; Given a single static lexical location SLOC, a dynamic lexical
;;; location CLOC holding the cell that replaces SLOC, and a single
;;; instruction INSTRUCTION that writes that location, create a new
;;; temporary dynamic lexical location D to hold the value of CLOC,
;;; replace all occurrences of SLOC in the outputs of I by D, and
;;; insert a new WRITE-CELL instruction after INSTRUCTION that puts
;;; the value of D in CLOC.
(defun replace-outputs (sloc cloc instruction)
  (let ((d (cleavir-ir:new-temporary))
        (cleavir-ir:*origin* (cleavir-ir:origin instruction))
	(cleavir-ir:*policy* (cleavir-ir:policy instruction))
        (cleavir-ir:*dynamic-environment*
          (cleavir-ir:dynamic-environment instruction)))
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
         instruction))
    #+nil
    (cleavir-hir-transformations:copy-propagate-1 d)))

(defun read-only-variable-p (location)
  (let ((definers (cleavir-ir:defining-instructions location)))
    (and definers (null (rest definers)))))

;;; Given a single static lexical location LOCATION, if the lexical is
;;; assigned to more than once, eliminate it by replacing all accesses
;;; to it by accesses to a corresponding CELL.  Otherwise, it can be
;;; allocated directly to the static environment.  FUNCTION-DAG is the
;;; function dag of the entire program.  INSTRUCTION-OWNERS is a hash
;;; table mapping an instruction to its owner.  OWNER is the owner of
;;; LOCATION.
(defun process-lexical-bind
    (lexical-bind function-dag instruction-owners)
  (let* ((owner (gethash lexical-bind instruction-owners))
         (variable (first (cleavir-ir:outputs lexical-bind)))
         ;; Determine all the functions (represented by
	 ;; ENTER-INSTRUCTIONs) that use (read or write) the location.
	 (users (functions-using-location variable instruction-owners))
	 ;; To that set, add the intermediate functions.
	 (enters (add-intermediate-functions users function-dag owner))
         (read-only-variable-p (read-only-variable-p variable))
         ;; A variable is closed over if it is used in a function that
         ;; is not the owner.
         (closed-over-p (rest users))
         ;; A variable becomes a value cell if it is closed over and
         ;; not read only.
         (value-cell-p (and closed-over-p (not read-only-variable-p)))
         ;; Compute a dictionary that associates each
         ;; ENTER-INSTRUCTION with a dynamic location.
         (dynamic-locations (allocate-dynamic-locations enters variable value-cell-p)))
    (loop for reference in (cleavir-ir:using-instructions variable)
          for instruction-owner = (gethash reference instruction-owners)
          for dynamic-location = (cdr (assoc instruction-owner dynamic-locations))
          do ;; FIXME: not everything is a reference yet. stuff like
             ;; THE needs to be fixed still to reference before using
             ;; lexical variable.
             (when (typep reference 'cleavir-ir:reference-instruction)
               (change-class reference 'cleavir-ir:assignment-instruction))
             (if value-cell-p
                 (replace-inputs variable dynamic-location reference)
                 (cleavir-ir:substitute-input dynamic-location variable reference)))
    (loop for instruction in (cleavir-ir:defining-instructions variable)
          for instruction-owner = (gethash instruction instruction-owners)
          for dynamic-location = (cdr (assoc instruction-owner dynamic-locations))
          do (if value-cell-p
                 (replace-outputs variable dynamic-location instruction)
                 (cleavir-ir:substitute-output dynamic-location variable instruction)))
    (when value-cell-p
      ;; Start by creating a CREATE-CELL-INSTRUCTION after the owner of
      ;; the static lexical location to be eliminated.
      (let ((cleavir-ir:*origin* (cleavir-ir:origin owner))
            (cleavir-ir:*policy* (cleavir-ir:policy owner))
            (cleavir-ir:*dynamic-environment*
              (cleavir-ir:dynamic-environment owner)))
        (cleavir-ir:insert-instruction-after
         (cleavir-ir:make-create-cell-instruction (cdr (assoc owner dynamic-locations)))
         lexical-bind)))
    (change-class lexical-bind 'cleavir-ir:assignment-instruction)
    ;; We do this step last, so that we are sure that the CREATE-CELL
    ;; and FETCH instructions are inserted immediately after the ENTER
    ;; instruction.
    (ensure-dynamic-location-available function-dag dynamic-locations owner instruction-owners)
    #+nil
    (cleavir-hir-transformations:copy-propagate-1 (first (cleavir-ir:inputs lexical-bind)))
    ;; Dynamic locations are eligible for copy propagation.
    (dolist (dynamic-location dynamic-locations)
      #+nil
      (cleavir-hir-transformations:copy-propagate-1 (cdr dynamic-location)))))

(defun process-catch
    (catch function-dag instruction-owners)
  (let* ((owner (gethash catch instruction-owners))
         (continuation (first (cleavir-ir:outputs catch)))
         ;; Determine all the functions (represented by
	 ;; ENTER-INSTRUCTIONs) that use (read or write) the location.
	 (users (functions-using-location continuation instruction-owners))
	 ;; To that set, add the intermediate functions.
	 (enters (add-intermediate-functions users function-dag owner))
         ;; Compute a dictionary that associates each
         ;; ENTER-INSTRUCTION with a dynamic location.
         (dynamic-locations (allocate-dynamic-locations enters continuation nil)))
    (loop for instruction in (cleavir-ir:using-instructions continuation)
          for instruction-owner = (gethash instruction instruction-owners)
          for dynamic-location = (cdr (assoc instruction-owner dynamic-locations))
          do (cleavir-ir:substitute-input dynamic-location continuation instruction))
    (loop for instruction in (cleavir-ir:defining-instructions continuation)
          for instruction-owner = (gethash instruction instruction-owners)
          for dynamic-location = (cdr (assoc instruction-owner dynamic-locations))
          do (cleavir-ir:substitute-output dynamic-location continuation instruction))
    ;; We do this step last, so that we are sure that the CREATE-CELL
    ;; and FETCH instructions are inserted immediately after the ENTER
    ;; instruction.
    (ensure-dynamic-location-available function-dag dynamic-locations owner instruction-owners)
    ;; Dynamic locations are eligible for copy propagation.
    (dolist (dynamic-location dynamic-locations)
      #+nil
      (cleavir-hir-transformations:copy-propagate-1 (cdr dynamic-location)))))

(defun process-lexical-variables (initial-instruction)
  (let ((instruction-owners (compute-instruction-owners initial-instruction))
        (function-dag (build-function-dag initial-instruction))
        (binds '())
        (catches '()))
    (cleavir-ir:map-instructions-arbitrary-order
     (lambda (instruction)
       (typecase instruction
         (cleavir-ir:lexical-bind-instruction (push instruction binds))
         (cleavir-ir:catch-instruction (push instruction catches))))
     initial-instruction)
    (dolist (bind binds)
      (process-lexical-bind bind function-dag instruction-owners))
    (dolist (catch catches)
      (process-catch catch function-dag instruction-owners))))

;;; Sort of a misnomer. It processes all lexical variables.
(defun process-captured-variables (initial-instruction)
  ;; Make sure everything is up to date.
  (cleavir-ir:reinitialize-data initial-instruction)
  (process-lexical-variables initial-instruction))
