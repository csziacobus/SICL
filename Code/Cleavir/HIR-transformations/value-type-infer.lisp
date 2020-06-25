;;;; Do value numbering, and constrain properties of value numbers
;;;; with type constraints.  Everything is basic block granularity for
;;;; speed and space efficiency, meaning there may be some loss of
;;;; precision for local assignments within basic blocks. However, I
;;;; think it is pretty much not worth the trouble since loss of
;;;; precision can only be observed by data with more than one
;;;; defining instruction with some sort of block local type
;;;; instruction.

;;;; The "value numbering" prepass analysis used here is designed to
;;;; make the actual type analysis sparse, in the sense that the type
;;;; analysis only needs to annotate value "numbers" instead of
;;;; number/congruency class + control point tuples, which is a huge
;;;; efficiency win, without loss of precision.

;;;; TODO actually use the executable flag to reanalyze merge points
;;;; for more precise type constraints.

;;;; TODO make value numbering actually aware of EQ-INSTRUCTION

(in-package #:cleavir-hir-transformations)

(defclass augmented-basic-block (cleavir-basic-blocks:basic-block)
  (;; Will this block actually get executed?
   (%executablep :accessor executablep :initarg :executablep)
   ;; Congruence classes of eq data represented by a value numbering
   ;; data structure.
   (%in-eq-data :accessor in-eq-data :initarg :in-eq-data)
   (%out-eq-data :accessor out-eq-data :initarg :out-eq-data)
   ;; For all incoming constraints.
   (%in-constraints :accessor in-constraints :initarg :in-constraints)
   ;; From out constraints coming from stuff like THE.
   ;; Right now basically always a copy of IN but will soon change.
   (%out-constraints :accessor out-constraints :initarg :out-constraints)
   ;; Used for asserting complementary constraints.
   (%branch-constraint :accessor branch-constraint :initarg :branch-constraint :initform nil)))

;; Need a fresh object for the value numbering table to enable sparse
;; analysis.
(defclass value-number () ())
;; Why do we need a phi value number? It is required for us to
;; fixpoint in DAGs like A -> B; B -> B; B -> C; C -> B. Essentially
;; normal value-numbers transition to phi-value-numbers, so called
;; since they resemble the contexts in which you see a phi, which then
;; do not change on additional iterations of the algorithm, enabling
;; easy fixpoint detection.
(defclass phi-value-number (value-number) ())

(defclass value-number-table ()
  ((%table :accessor table :initarg :table)))

(defun make-value-number-table (&key (size 0))
  (make-instance 'value-number-table :table (make-hash-table :size size)))

(defun make-value-number () (make-instance 'value-number))
(defun make-phi-value-number () (make-instance 'phi-value-number))

(defun compute-block-in-eq-data (block predecessors initial-pass-p)
  (cond ((null predecessors)
         (assert (and (typep (cleavir-basic-blocks:first-instruction block)
                             'cleavir-ir:enter-instruction)
                      initial-pass-p))
         (setf (in-eq-data block) (make-value-number-table)))
        ((null (rest predecessors))
         ;; Can share the same value number table in this case because
         ;; the in tables should never get modified during the block
         ;; local phase.
         (setf (in-eq-data block) (out-eq-data (first predecessors))))
        (t
         ;; Basically intersect over all predecessor value tables.
         (let* ((pred-tables (mapcar #'out-eq-data predecessors))
                (initialized-tables
                  (remove-if (lambda (table)
                               (zerop (hash-table-count table)))
                             pred-tables :key #'table))
                (value-table (if initial-pass-p
                                 (make-value-number-table
                                  :size
                                  (loop for table in initialized-tables
                                        minimize (hash-table-count (table table))))
                                 (in-eq-data block))))
           (when (not initial-pass-p)
             (assert (equal initialized-tables pred-tables)))
           (maphash (lambda (datum number)
                      (let ((all-same t)
                            (overdefined nil))
                        (dolist (table (rest initialized-tables))
                          (let ((other-number (gethash datum (table table))))
                            ;; When the other number exists and is
                            ;; different, then the value is
                            ;; overdefined.
                            (when other-number
                              (unless (eq number other-number)
                                (setf all-same nil)
                                (setf overdefined t)
                                (return)))))
                        (when all-same
                          (setf (gethash datum (table value-table))
                                number))
                        (when overdefined
                          (if initial-pass-p
                              (setf (gethash datum (table value-table))
                                    (make-value-number))
                              ;; Only allocate a new phi value number
                              ;; during reanalysis if it has not been
                              ;; reanalyzed as such yet to prevent
                              ;; infinite loops.

                              ;; Why does this work?

                              ;; In the initial reanalysis pass, all
                              ;; predecessor value tables are already
                              ;; initialized. Therefore, we are
                              ;; guaranteed to get a fresh congruency
                              ;; class distinct from all the
                              ;; predecessors. As flow propagation
                              ;; goes around and reinitializes all the
                              ;; predecessors, the true congruency
                              ;; class will stabilize the second time
                              ;; around.
                              (unless (typep (gethash datum (table value-table)) 'phi-value-number)
                                (setf (gethash datum (table value-table))
                                      (make-phi-value-number)))))))
                    (table (first initialized-tables)))
           (setf (in-eq-data block) value-table)))))

;;; Transfer in data to out data. Return whether it feels like something has changed.
(defun block-value-transfer (block initial-pass-p)
  (let* ((in-eq-data (in-eq-data block))
         (in-table (table in-eq-data))
         (out-eq-data (out-eq-data block))
         (out-table (table out-eq-data))
         ;; Need a temporary table to accumulate the effects of
         ;; assignments without yet committing.
         (temp-table (make-hash-table :size (abs
                                             (- (hash-table-count out-table)
                                                (hash-table-count in-table)))))
         (changed nil))
    (cleavir-basic-blocks:map-basic-block-instructions
     (lambda (instruction)
       (typecase instruction
         (cleavir-ir:assignment-instruction
          (let* ((input (first (cleavir-ir:inputs instruction)))
                 (output (first (cleavir-ir:outputs instruction)))
                 (input-number (or (gethash input temp-table)
                                   (gethash input in-table)
                                   (or
                                    ;; Assert that this inputs define
                                    ;; does not occur after its first
                                    ;; use in the forward flow order
                                    ;; (pseudotopological).
                                    (assert (not (typep input 'cleavir-ir:lexical-location)))
                                    ;; For any location that isn't a
                                    ;; lexical location, use it
                                    ;; literally.
                                    input))))
            (setf (gethash output temp-table) input-number)))
         (t
          ;; This is where having known functions would plug into
          ;; recording the actual value numbers. For now, just
          ;; invalidate whatever was in the table and assign a new
          ;; value number to this datum if it previously existed. If
          ;; it's not in the table, then leave it as
          ;; nothing. Basically treating all non-assignment
          ;; instructions as totally opaque.
          (dolist (output (cleavir-ir:outputs instruction))
            (setf (gethash output temp-table)
                  (if initial-pass-p
                      (make-value-number)
                      ;; Reuse an existing number. It will get
                      ;; overwritten with the right stuff if it's bad.
                      (progn
                        (assert (gethash output out-table))
                        (gethash output out-table))))))))
     block)
    ;; Commit the existing or new value numbers of existing data
    ;; to the out table.
    (maphash (lambda (datum in-number)
               (let* ((temp-number (gethash datum temp-table))
                      (out-number (gethash datum out-table))
                      (new-out-number (or temp-number in-number)))
                 (unless (eq out-number new-out-number)
                   (setf (gethash datum out-table) new-out-number)
                   (setf changed t))))
             in-table)
    ;; Inform the out table of the value numbers of new data. Should
    ;; really only happen in the initial reverse post-order
    ;; pass... maybe? This is because any new value appearing block
    ;; locally won't need to be reanalyzed pretty sure.
    (when initial-pass-p
      (maphash (lambda (datum temp-number)
                 (let ((out-number (gethash datum out-table)))
                   (unless (eq out-number temp-number)
                     (setf (gethash datum out-table) temp-number)
                     (setf changed t))))
               temp-table))
    changed))

(defun value-number (start)
  (let* ((initial-ordering
           (cleavir-utilities::depth-first-search-reverse-post-order
            start
            #'cleavir-basic-blocks:successors))
         (reanalyze (and '() initial-ordering)))
    ;; Drain the initial ordering.
    (loop
      (when (null initial-ordering)
        (return))
      (let ((block (pop initial-ordering)))
        (compute-block-in-eq-data block (cleavir-basic-blocks:predecessors block) t)
        (block-value-transfer block t)
        (dolist (succ (cleavir-basic-blocks:successors block))
          ;; Backedge.
          (unless (member succ initial-ordering)
            (push succ reanalyze)))))
    ;; Now that the initial forward flow is done, we fix up
    ;; blocks-to-be-reanalyzed and probably replace a few
    ;; value-numbers with phi-numbers.
    (loop
      (when (null reanalyze)
        (return))
      (let ((block (pop reanalyze)))
        (compute-block-in-eq-data block (cleavir-basic-blocks:predecessors block) nil)
        (when (block-value-transfer block nil)
          (dolist (succ (cleavir-basic-blocks:successors block))
            (pushnew succ reanalyze)))))))

;;; In Cleavir, actual instructions are the only thing that mark
;;; control points, so to build a mapping from control points to the
;;; values of data, we basically create a hash table mapping
;;; INSTRUCTION -> ((datum . constraint))

;;; Except it's only basic block granularity right now. If we wanted
;;; instruction level granularity we're going to need much better data
;;; structures.

(defclass constraint ()
  ((%value :accessor constraint-value :initarg :value)))

(defclass type-constraint (constraint)
  ((%ctype :accessor type-constraint-ctype :initarg :ctype)))

(defclass typep-constraint (type-constraint) ())
(defclass <-constraint (type-constraint) ())
(defclass >-constraint (type-constraint) ())

(defclass constraint-table ()
  ((%table :accessor table :initform (make-hash-table))))

(defun make-constraint-table ()
  (make-instance 'constraint-table))

(defun make-typeq-constraint (value ctype)
  (make-instance 'typep-constraint :value value :ctype ctype))

;;; FIXME this is only one constraint right now.
(defun add-constraint-to-table (constraint-table value-number constraint)
  (setf (gethash value-number constraint-table) constraint))

(defun lookup-constraint-in-table (constraint-table value-number)
  (gethash value-number constraint-table))

(defun single-def (location)
  (null (rest (cleavir-ir:defining-instructions location))))

(defgeneric constrain-branch-instruction (instruction block system))

(defmethod constrain-branch-instruction (instruction block system))

(defmethod constrain-branch-instruction ((instruction cleavir-ir:eq-instruction) block system)
  ;; We really should do something with this.
  )

;;; Rethink what it means to EXECUTE.
(defmethod constrain-branch-instruction ((instruction cleavir-ir:typeq-instruction) block system)
  (let* ((input (first (cleavir-ir:inputs instruction)))
         (input-value (gethash input (table (out-eq-data block))))
         (ctype (cleavir-ir:value-type instruction))
         (successors (cleavir-ir:successors instruction))
         (then (first successors))
         (else (second successors))
         (then-block (find then (cleavir-basic-blocks:successors block)
                           :key #'cleavir-basic-blocks:first-instruction))
         (else-block (find else (cleavir-basic-blocks:successors block)
                           :key #'cleavir-basic-blocks:first-instruction))
         ;; FIXME: replace with ensure gethash or something
         (existing (or (gethash input-value (table (in-constraints block)))
                       (setf (gethash input-value (table (in-constraints block)))
                             (make-typeq-constraint input-value (cleavir-ctype:top nil)))))
         (existing-ctype (type-constraint-ctype existing)))
    (cond ((cleavir-ctype:subtypep existing-ctype ctype system)
           (print "ALWAYS TRUE")
           ;; Always taken, so mark only the then successor as
           ;; non-executable.
           (setf (executablep else-block) nil))
          ;; XXX: Switch this to bottom-p when things are worked out
          ;; more.
          ((cleavir-ctype:subtypep (cleavir-ctype:conjoin/2 ctype existing-ctype system)
                                   (cleavir-ctype:bottom system)
                                   nil)
           (print "NEVER TRUE")
           ;; Never executable.

           ;; TODO make this effect the worklist as well, so that
           ;; merge points for unreachable branches are not taken
           ;; into account.
           (setf (executablep then-block) nil)))
    (setf (branch-constraint block)
          ;; Do NOT intersect here.
          (make-typeq-constraint input-value ctype))))

(defun union-constraint-into-table (constraint constraint-table system)
  (let* ((value (constraint-value constraint))
         (table (table constraint-table))
         (existing (gethash value table))
         (new (type-constraint-ctype constraint)))
    (setf (gethash value table)
          (make-typeq-constraint
           value
           (if existing
               ;; FIXME add system arugment
               (cleavir-ctype:disjoin/2 new (type-constraint-ctype existing) system)
               new)))))

(defun compute-in-constraints (block predecessors system)
  ;; Take the out sets of the predecessors and the branch conditions
  ;; of the predecessors and merge them. Type union is our meet
  ;; operation.
  (case (length predecessors)
    (0
     (assert (typep (cleavir-basic-blocks:first-instruction block)
                    'cleavir-ir:enter-instruction))
     (setf (in-constraints block) (make-constraint-table)))
    (t
     (let ((constraint-table (make-constraint-table)))
       (dolist (predecessor predecessors)
         (let* ((branch-constraint (branch-constraint predecessor))
                (branch-value
                  (and branch-constraint
                       (constraint-value branch-constraint)))
                (negatep
                  ;; Check the relationship of this block with respect
                  ;; to the predecessor.  Cannot just use block
                  ;; successors since instruction successors may
                  ;; differ :(.
                  (and branch-constraint
                       (eq (cleavir-basic-blocks:first-instruction block)
                           (second (cleavir-ir:successors
                                    (cleavir-basic-blocks:last-instruction
                                     predecessor)))))))
           (when branch-constraint
             ;; Intersect the constraint with any existing constraints
             ;; based on the branch taken in the predecessor then
             ;; union it in.
             (let* ((value (constraint-value branch-constraint))
                    (existing (gethash value (table (out-constraints predecessor))))
                    (new (if negatep
                             (cleavir-ctype:negate (type-constraint-ctype branch-constraint) system)
                             (type-constraint-ctype branch-constraint))))
               (union-constraint-into-table
                (make-typeq-constraint
                 value
                 (if existing
                     (cleavir-ctype:conjoin/2 new (type-constraint-ctype existing) system)
                     new))
                constraint-table
                system)))
           ;; Now union in the rest.
           (maphash
            (lambda (value constraint)
              (unless (eq value branch-value)
                (union-constraint-into-table constraint constraint-table system))
              ;; If there is no constraint in any of the predecessors,
              ;; that is an implicit T type, so make sure to take note of
              ;; that.
              (dolist (predecessor predecessors)
                (unless (gethash value (table (out-constraints predecessor)))
                  (union-constraint-into-table
                   (make-typeq-constraint value (cleavir-ctype:top nil))
                   constraint-table
                   system))))
            (table (out-constraints predecessor)))))
       (setf (in-constraints block) constraint-table))))
  (in-constraints block))

(defun subconstraintp (constraint1 constraint2 system)
  ;; ASSUMPTION type constraints are the only constraint.
  (cleavir-ctype:subtypep (type-constraint-ctype constraint1)
                          (type-constraint-ctype constraint2)
                          system))

;;; The block local portion is in charge of killing or augmenting the
;;; constraints in a block.
;;; The global portion merges information from the blocks, especially
;;; at merge points.
(defun analyze-types (start system)
  ;; Type inference is a forward data-flow problem.
  (let ((worklist (cleavir-utilities::depth-first-search-reverse-post-order
                   start
                   #'cleavir-basic-blocks:successors)))
    (loop
      (when (null worklist)
        (return))
      (let* ((block (pop worklist))
             (last (cleavir-basic-blocks:last-instruction block))
             (in-constraints (compute-in-constraints block
                                                     (cleavir-basic-blocks::predecessors block)
                                                     system))
             (in-table (table in-constraints))
             (out-constraints-data (out-constraints block))
             (out-table (table out-constraints-data))
             (changed nil))
        ;; We have in constraints, so make the new out constraints
        ;; based on the in constraints and then add the final branch
        ;; constraint.

        ;; For now, OUT = IN. The only thing is that we check whether
        ;; we have reached a fixpoint for this block.
        (maphash (lambda (value in-constraint)
                   (let* ((out-constraint (gethash value out-table)))
                     (if out-constraint
                         ;; Test if the IN constraint is narrower than
                         ;; the OUT constraint. If not, then don't
                         ;; mark changed.
                         (setf changed (not (subconstraintp out-constraint in-constraint system)))
                         (progn
                           (setf (gethash value out-table) in-constraint)
                           (setf changed t)))))
                 in-table)
        (when changed
          (dolist (succ (cleavir-basic-blocks:successors block))
            ;; Use pushnew so we preserve our reverse post order initial walk.
            (pushnew succ worklist)))
        ;; Don't need to check for changed here i think because the
        ;; general maphash above does... XXX
        (when (rest (cleavir-ir:successors last))
          (constrain-branch-instruction last block system))))))

;;; The reason why we track executablep on the blocks is that
;;; unreachable blocks will actually make the assertion at merge points
;;; better, if one of the predecessor blocks is determined not
;;; executable.
(defun eliminate-redundant-typeqs (initial-instruction system)
  (let* ((basic-blocks (cleavir-basic-blocks:basic-blocks initial-instruction))
         (instruction-basic-blocks (cleavir-basic-blocks:instruction-basic-blocks basic-blocks))
         (starting-blocks '()))
    (dolist (block basic-blocks)
      (change-class block 'augmented-basic-block
                    :executablep t
                    :out-eq-data (make-value-number-table)
                    :out-constraints (make-constraint-table))
      (when (typep (cleavir-basic-blocks:first-instruction block) 'cleavir-ir:enter-instruction)
        (push block starting-blocks)))
    (dolist (start starting-blocks)
      (value-number start)
      #+(or)
      (let ((list (cleavir-utilities::depth-first-search-reverse-post-order
                   start
                   #'cleavir-basic-blocks:successors)))
        (dolist (block list)
          (print block)
          (format t "~&in: ~a" (table (in-eq-data block)))
          (format t "~&out: ~a" (table (out-eq-data block))))))
    (dolist (start starting-blocks)
      (analyze-types start system)
      #+(or)
      (let ((list (cleavir-utilities::depth-first-search-reverse-post-order
                   start
                   #'cleavir-basic-blocks:successors)))
        (dolist (block list)
          (print block)
          (format t "~&in: ~a" (table (in-constraints block)))
          (format t "~&out: ~a" (table (out-constraints block)))
          (format t "~&executable: ~a" (executablep block)))))
    (dolist (block basic-blocks)
      (when (executablep block)
        (let ((last (cleavir-basic-blocks:last-instruction block)))
          (typecase last
            (cleavir-ir:typeq-instruction
             (let* ((succs (cleavir-ir:successors last))
                    (then (first succs))
                    (else (second succs)))
               (when (not (executablep (gethash then instruction-basic-blocks)))
                 (format t "~& deleting typeq: ~a" (cleavir-ir:value-type last))
                 (cleavir-ir:bypass-instruction else last))
               (when (not (executablep (gethash else instruction-basic-blocks)))
                 (format t "~& deleting typeq: ~a" (cleavir-ir:value-type last))
                 (cleavir-ir:bypass-instruction then last))))))))
    (cleavir-ir:reinitialize-data initial-instruction)
    (cleavir-ir:set-predecessors initial-instruction)))
