(cl:in-package #:cleavir-remove-useless-instructions)

(defgeneric instruction-may-be-removed-p (instruction))

(defmethod instruction-may-be-removed-p (instruction)
  (and (= (length (cleavir-ir:successors instruction)) 1)
       (loop for output in (cleavir-ir:outputs instruction)
	     always (null (cleavir-ir:using-instructions output)))))

(defmethod instruction-may-be-removed-p
    ((instruction cleavir-ir:side-effect-mixin))
  nil)

(defmethod instruction-may-be-removed-p
    ((instruction cleavir-ir:enter-instruction))
  nil)

(defmethod instruction-may-be-removed-p
    ((instruction cleavir-ir:catch-instruction))
  ;; using-instructions will be incorrect, therefore
  nil)

(defun remove-useless-instructions-with-worklist (worklist function)
  (let ((deleted '()))
    (loop (when (null worklist) (return))
          (let ((instruction (pop worklist)))
            (when (and (instruction-may-be-removed-p instruction)
                       (every (lambda (output)
                                (null (cleavir-ir:using-instructions output)))
                              (cleavir-ir:outputs instruction)))
              (dolist (output (cleavir-ir:outputs instruction))
                (setf (cleavir-ir:defining-instructions output)
                      (remove instruction (cleavir-ir:defining-instructions output))))
              (dolist (input (cleavir-ir:inputs instruction))
                (setf (cleavir-ir:using-instructions input)
                      (remove instruction (cleavir-ir:using-instructions input)))
                (dolist (defining-instruction (cleavir-ir:defining-instructions input))
                  (push defining-instruction worklist)))
              (funcall function instruction))))
    deleted))

(defun remove-useless-instructions (initial-instruction)
  (remove-useless-instructions-with-worklist (cleavir-ir:instructions-of-type initial-instruction t)
                                             #'cleavir-ir:delete-instruction))

;;; An incremental version of remove-useless-instructions meant for
;;; clients which know where in the graph a potentially useless
;;; instruction has appeared.
(defun remove-useless-instructions-from (instructions)
  (remove-useless-instructions-with-worklist instructions #'cleavir-ir:delete-instruction))
