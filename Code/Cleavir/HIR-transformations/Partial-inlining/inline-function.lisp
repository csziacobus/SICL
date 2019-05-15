(cl:in-package #:cleavir-partial-inlining)

;;; Cut and paste a function to inline - i.e. don't copy much of anything, which is nice,
;;; but means the original is destroyed.
(defun interpolate-function (call enter node)
  (let ((returns '())
        (unwinds '())
        (target-enter (instruction-owner call))
        (old-dynenv (cleavir-ir:dynamic-environment enter))
        (call-dynenv (cleavir-ir:dynamic-environment call))
        (cells (cleavir-ir:inputs (cleavir-hir-transformations:enclose-instruction node))))
    ;; Update the ownerships of each local instruction and datum and
    ;; find the exit point instructions. Also update the dynamic
    ;; environments of instructions whose dynamic environment is the
    ;; same as the one established by ENTER.
    (cleavir-ir:map-local-instructions
     (lambda (instruction)
       (setf (instruction-owner instruction) target-enter)
       (when (eq (cleavir-ir:dynamic-environment instruction)
                 old-dynenv)
         (setf (cleavir-ir:dynamic-environment instruction)
               call-dynenv))
       (dolist (input (cleavir-ir:inputs instruction))
         (when (eq (location-owner input) enter)
           (setf (location-owner input) target-enter)))
       (dolist (output (cleavir-ir:outputs instruction))
         (when (eq (location-owner output) enter)
           (setf (location-owner output) target-enter)))
       (when (typep instruction 'cleavir-ir:return-instruction)
         (push instruction returns))
       (when (typep instruction 'cleavir-ir:unwind-instruction)
         (push instruction unwinds)))
     enter)
    (dolist (fetch (cleavir-ir:using-instructions (cleavir-ir:static-environment enter)))
      (let* ((inputs (cleavir-ir:inputs fetch))
             (index (cleavir-ir:value (second inputs)))
             (cell (first (cleavir-ir:outputs fetch)))
             (real-cell (nth index cells)))
        (dolist (use (cleavir-ir:using-instructions cell))
          (nsubstitute real-cell cell (cleavir-ir:inputs use))
          (push use (cleavir-ir:using-instructions real-cell)))
        (cleavir-ir:delete-instruction fetch)))
    ;; We need to alter these. We find them before doing any alteration-
    ;; interleaving modification and finds results in unfortunate effects.
    ;; Make appropriate assignments to do the ENTER's task.
    (loop with cleavir-ir:*policy* = (cleavir-ir:policy call)
          with cleavir-ir:*dynamic-environment* = call-dynenv
          for location in (cleavir-ir:parameters enter)
          for arg in (rest (cleavir-ir:inputs call))
          for assign = (cleavir-ir:make-assignment-instruction arg location)
          do (cleavir-ir:insert-instruction-before assign call))
    ;; Turn any unwinds in the body to the function being inlined into
    ;; into direct control transfers.
    (loop with target-enter = (instruction-owner call)
          for unwind in unwinds
          for destination = (cleavir-ir:destination unwind)
          ;; Recapitulates local-catch-p in inline-one-instruction.lisp, a bit.
          when (eq (instruction-owner destination) target-enter)
            ;; it's local: replace it. (If not local, there is nothing to do.)
            ;; (Similar to the unwind-instruction method on inline-one-instruction)
            do (let* ((target (nth (cleavir-ir:unwind-index unwind)
                                   (cleavir-ir:successors destination)))
                      (nop (let ((cleavir-ir:*policy* (cleavir-ir:policy unwind))
                                 (cleavir-ir:*dynamic-environment* (cleavir-ir:dynamic-environment unwind)))
                             (cleavir-ir:make-nop-instruction (list target)))))
                 (cleavir-ir:bypass-instruction nop unwind)))
    ;; Fix up the return values, and replace return instructions with NOPs that go to after the call.
    (loop with caller-values = (first (cleavir-ir:outputs call))
          with next = (first (cleavir-ir:successors call))
          for return in returns
          for values = (first (cleavir-ir:inputs return))
          do (cleavir-ir:replace-datum caller-values values)
             (let ((nop (let ((cleavir-ir:*policy* (cleavir-ir:policy return))
                              (cleavir-ir:*dynamic-environment* (cleavir-ir:dynamic-environment return)))
                          (cleavir-ir:make-nop-instruction (list next)))))
               (cleavir-ir:bypass-instruction nop return))))
  ;; Replace the call with a regular control arc into the function.
  (cleavir-ir:bypass-instruction (first (cleavir-ir:successors enter)) call)
  ;; Done!
  (values))

;;; Remvoe an enter instruction from the list of predecessors of its successors.
(defun disconnect-predecessor (instruction)
  (dolist (successor (cleavir-ir:successors instruction))
    (setf (cleavir-ir:predecessors successor)
          (delete instruction (cleavir-ir:predecessors successor)))))

(defun attach-predecessor (instruction)
  (dolist (successor (cleavir-ir:successors instruction))
    (push instruction (cleavir-ir:predecessors successor))))

(defmethod inline-function (initial call enter node mapping)
  (let* ((*original-enter-instruction* enter)
         (*instruction-mapping* (make-hash-table :test #'eq))
         ;; Used for catch/unwind (local-catch-p)
         (*target-enter-instruction* (instruction-owner call))
         (cells (cleavir-ir:inputs (cleavir-hir-transformations:enclose-instruction node)))
         (initial-environment (cleavir-ir:parameters enter))
         ;; *policy* is bound closely for these bindings to make especially sure
         ;; that inlined instructions have the policy of the source function,
         ;; rather than the call.
         (call-arguments
           (loop with cleavir-ir:*policy* = (cleavir-ir:policy call)
                 with cleavir-ir:*dynamic-environment*
                   = (cleavir-ir:dynamic-environment call)
                 for location in initial-environment
                 for arg in (rest (cleavir-ir:inputs call))
                 for temp = (cleavir-ir:new-temporary)
                 for assign = (cleavir-ir:make-assignment-instruction arg temp)
                 do (cleavir-ir:insert-instruction-before assign call)
                    (setf (instruction-owner assign) *target-enter-instruction*)
                    (add-to-mapping mapping location temp)
                    (setf (location-owner temp) *target-enter-instruction*)
                 collect temp))
         (dynenv (cleavir-ir:dynamic-environment call))
         (function-temp (cleavir-ir:new-temporary))
         ;; This is used by the "partial" enter, but not actually connected.
         (fake-dynenv (cleavir-ir:new-temporary))
         (new-enter (cleavir-ir:clone-instruction enter
                      :dynamic-environment fake-dynenv))
         (enc (let ((cleavir-ir:*policy* (cleavir-ir:policy call))
                    (cleavir-ir:*dynamic-environment* dynenv))
                (cleavir-ir:make-enclose-instruction function-temp call new-enter))))
    ;; Map the old inner dynenv to the outer dynenv.
    (add-to-mapping mapping
                    (cleavir-ir:dynamic-environment enter)
                    (cleavir-ir:dynamic-environment call))
    ;; the new ENTER shares policy and successor, but has no parameters.
    (setf (cleavir-ir:lambda-list new-enter) '()
          ;; the temporary is the closure variable.
          (cleavir-ir:outputs new-enter) (list (cleavir-ir:new-temporary) fake-dynenv))
    ;; Ensure that the enc's successor doens't contain enc as a
    ;; predecessor, since this is outdated information.
    (disconnect-predecessor enc)
    (cleavir-ir:insert-instruction-before enc call)
    (setf (cleavir-ir:inputs call) (cons function-temp call-arguments))
    ;; If we're fully inlining a function, we want to use the call instruction's
    ;; output instead of the callee's return values.
    ;; FIXME: Not sure what to do if we're not fully inlining.
    (loop with caller-values = (first (cleavir-ir:outputs call))
          for return in (cleavir-ir:local-instructions-of-type
                         enter 'cleavir-ir:return-instruction)
          for input = (first (cleavir-ir:inputs return))
          do (add-to-mapping mapping input caller-values))
    ;; Only works for full inlining, but wire up any fetch cells to
    ;; the real cells submitted.
    (dolist (fetch (cleavir-ir:using-instructions (cleavir-ir:static-environment enter)))
      (let* ((inputs (cleavir-ir:inputs fetch))
             (index (cleavir-ir:value (second inputs)))
             (cell (first (cleavir-ir:outputs fetch))))
        (add-to-mapping mapping cell (nth index cells))))
    ;; Do the actual inlining.
    ;; FIXME: Once an inlining stops, all remaining residual functions should have
    ;; any variables live at that point added as inputs, etc.
    (let ((worklist (list (make-instance 'worklist-item
                            :enclose-instruction enc
                            :call-instruction call
                            :enter-instruction new-enter
                            :mapping mapping))))
      (loop until (null worklist)
            do (let* ((item (pop worklist))
                      (enter (enter-instruction item))
                      (successor (first (cleavir-ir:successors enter))))
                 (setf worklist
                       (append (inline-one-instruction
                                (enclose-instruction item)
                                (call-instruction item)
                                enter
                                successor
                                (mapping item))
                               worklist)))))))
