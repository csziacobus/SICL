(cl:in-package #:cleavir-ast)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Class SLOT-READ-AST.
;;;
;;; This AST can be used to read a slot from a standard instance.  It
;;; has two children, an AST that must have a standard instance as its
;;; value, and an AST that must have a fixnum as its value and that
;;; indicates a slot number (starting from 0).  This AST generates a
;;; single value, namely the contents of the slot with the number given.

(defclass slot-read-ast (ast dynamic-environment-input-ast-mixin one-value-ast-mixin)
  ((%object-ast :initarg :object-ast :reader object-ast)
   (%slot-number-ast :initarg :slot-number-ast :reader slot-number-ast)))

(cleavir-io:define-save-info slot-read-ast
  (:object-ast object-ast)
  (:slot-number-ast slot-number-ast))

(defmethod children ((ast slot-read-ast))
  (list (object-ast ast) (slot-number-ast ast)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Class SLOT-WRITE-AST.
;;;
;;; This AST can be used to write a slot in a standard instance.  It
;;; has three children, an AST that must have a standard instance as
;;; its value, an AST that must have a fixnum as its value and that
;;; indicates a slot number (starting from 0), and an AST that
;;; generates the new value to store in the slot.  This AST generates
;;; no values.  An attempt to compile this AST in a context where a
;;; value is needed will result in an error being signaled.

(defclass slot-write-ast (ast no-value-ast-mixin dynamic-environment-input-ast-mixin)
  ((%object-ast :initarg :object-ast :reader object-ast)
   (%slot-number-ast :initarg :slot-number-ast :reader slot-number-ast)
   (%value-ast :initarg :value-ast :reader value-ast)))

(cleavir-io:define-save-info slot-write-ast
  (:object-ast object-ast)
  (:slot-number-ast slot-number-ast)
  (:value-ast value-ast))

(defmethod children ((ast slot-write-ast))
  (list (object-ast ast) (slot-number-ast ast) (value-ast ast)))
