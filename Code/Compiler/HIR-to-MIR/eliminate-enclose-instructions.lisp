(cl:in-package #:sicl-hir-to-mir)

(defclass entry-point-input (cleavir-ir:immediate-input)
  ((%enter-instruction :initarg :enter-instruction :reader enter-instruction)))

;;; Replace each ENTER instruction that is an immediate child of
;;; ENTER-INSTRUCTION with an AREF-instruction.
(defun eliminate-enclose-instructions (client enter-instruction)
  (declare (ignore client))
  (let ((static-environment-location
          (cleavir-ir:static-environment enter-instruction)))
    (cleavir-ir:map-local-instructions
     (lambda (instruction)
       (when (typep instruction 'cleavir-ir:enclose-instruction)
         (let ((enclose-function-lexical-location
                 (make-instance 'cleavir-ir:lexical-location
                   :name (gensym "enclose-function")))
               (static-input-1
                 (make-instance 'cleavir-ir:constant-input
                   :value 1))
               (entry-point-input
                 (make-instance 'entry-point-input
                   :value 0
                   :enter-instruction (cleavir-ir:code instruction))))
           (cleavir-ir:insert-instruction-before
            (make-instance 'cleavir-ir:aref-instruction
              :boxed-p t
              :simple-p t
              :element-type t
              :inputs (list static-environment-location static-input-1)
              :output enclose-function-lexical-location)
            instruction)
           (cleavir-ir:insert-instruction-after
            (make-instance 'cleavir-ir:multiple-to-fixed-instruction
              :output (first (cleavir-ir:outputs instruction)))
            instruction)
           (change-class instruction
                         'cleavir-ir:funcall-instruction
                         :inputs (list* enclose-function-lexical-location
                                        entry-point-input
                                        (cleavir-ir:inputs instruction))
                         :outputs '()))))
     enter-instruction)))
