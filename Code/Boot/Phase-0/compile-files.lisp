(cl:in-package #:sicl-boot-phase-0)

(defun compile-files (client environment)
  (flet ((cf (name)
           (format *trace-output* "Compiling file ~s~%" name)
           (compile-file client name environment)))
    (cf "CLOS/t-defclass.lisp")
    (cf "CLOS/function-defclass.lisp")
    (cf "CLOS/standard-object-defclass.lisp")
    (cf "CLOS/metaobject-defclass.lisp")
    (cf "CLOS/method-defclass.lisp")
    (cf "CLOS/standard-method-defclass.lisp")
    (cf "CLOS/standard-accessor-method-defclass.lisp")
    (cf "CLOS/standard-reader-method-defclass.lisp")
    (cf "CLOS/standard-writer-method-defclass.lisp")
    (cf "CLOS/slot-definition-defclass.lisp")
    (cf "CLOS/standard-slot-definition-defclass.lisp")
    (cf "CLOS/direct-slot-definition-defclass.lisp")
    (cf "CLOS/effective-slot-definition-defclass.lisp")
    (cf "CLOS/standard-direct-slot-definition-defclass.lisp")
    (cf "CLOS/standard-effective-slot-definition-defclass.lisp")
    (cf "CLOS/method-combination-defclass.lisp")
    (cf "CLOS/specializer-defclass.lisp")
    (cf "CLOS/class-defclass.lisp")
    (cf "CLOS/real-class-defclass.lisp")
    (cf "CLOS/regular-class-defclass.lisp")
    (cf "CLOS/standard-class-defclass.lisp")
    (cf "CLOS/funcallable-standard-class-defclass.lisp")
    (cf "CLOS/built-in-class-defclass.lisp")
    (cf "CLOS/forward-referenced-class-defclass.lisp")
    (cf "CLOS/eql-specializer-defclass.lisp")
    (cf "CLOS/funcallable-standard-object-defclass.lisp")
    (cf "CLOS/simple-function-defclass.lisp")
    (cf "CLOS/generic-function-defclass.lisp")
    (cf "CLOS/standard-generic-function-defclass.lisp")
    (cf "Cons/cons-defclass.lisp")
    (cf "Cons/list-defclass.lisp")
    (cf "Cons/null-defclass.lisp")
    (cf "Cons/accessor-defuns.lisp")
    (cf "Cons/cxr.lisp")
    (cf "Cons/setf-cxr.lisp")
    (cf "Cons/null-defun.lisp")
    (cf "Cons/list-defun.lisp")
    (cf "Cons/list-star-defun.lisp")
    (cf "Cons/list-length-defun.lisp")
    (cf "Cons/mapcar-defun.lisp")
    (cf "Cons/mapcan-defun.lisp")
    (cf "Cons/mapc-defun.lisp")
    (cf "Cons/mapcon-defun.lisp")
    (cf "Cons/mapl-defun.lisp")
    (cf "Cons/maplist-defun.lisp")
    (cf "Cons/member-defun.lisp")
    (cf "Cons/member-if-defun.lisp")
    (cf "Cons/member-if-not-defun.lisp")
    (cf "Cons/union-defun.lisp")
    (cf "Cons/nunion-defun.lisp")
    (cf "Cons/intersection-defun.lisp")
    (cf "Cons/nintersection-defun.lisp")
    (cf "Cons/set-difference-defun.lisp")
    (cf "Cons/nset-difference-defun.lisp")
    (cf "Cons/set-exclusive-or-defun.lisp")
    (cf "Cons/nset-exclusive-or-defun.lisp")
    (cf "Cons/subsetp-defun.lisp")
    (cf "Cons/endp-defun.lisp")
    (cf "Cons/make-list-defun.lisp")
    (cf "Cons/acons-defun.lisp")
    (cf "Cons/adjoin-defun.lisp")
    (cf "Cons/append-defun.lisp")
    (cf "Cons/revappend-defun.lisp")
    (cf "Cons/nconc-defun.lisp")
    (cf "Cons/nreconc-defun.lisp")
    (cf "Cons/assoc-defun.lisp")
    (cf "Cons/assoc-if-defun.lisp")
    (cf "Cons/assoc-if-not-defun.lisp")
    (cf "Cons/rassoc-defun.lisp")
    (cf "Cons/rassoc-if-defun.lisp")
    (cf "Cons/rassoc-if-not-defun.lisp")
    (cf "Cons/butlast-defun.lisp")
    (cf "Cons/nbutlast-defun.lisp")
    (cf "Cons/copy-alist-defun.lisp")
    (cf "Cons/copy-list-defun.lisp")
    (cf "Cons/copy-tree-defun.lisp")
    (cf "Cons/tree-equal-defun.lisp")
    (cf "Cons/getf-defun.lisp")
    (cf "Cons/get-properties-defun.lisp")
    (cf "Cons/last-defun.lisp")
    (cf "Cons/make-bindings-defun.lisp")
    (cf "Cons/sublis-defun.lisp")
    (cf "Cons/nsublis-defun.lisp")
    (cf "Cons/subst-defun.lisp")
    (cf "Cons/nsubst-defun.lisp")
    (cf "Cons/subst-if-defun.lisp")
    (cf "Cons/nsubst-if-defun.lisp")
    (cf "Cons/subst-if-not-defun.lisp")
    (cf "Cons/nsubst-if-not-defun.lisp")
    (cf "Cons/nth-defun.lisp")
    (cf "Cons/setf-nth-defun.lisp")
    (cf "Cons/nthcdr-defun.lisp")
    (cf "Cons/pairlis-defun.lisp")
    (cf "Cons/ldiff-defun.lisp")
    (cf "Cons/tailp-defun.lisp")
    (cf "Sequence/sequence-defclass.lisp")
    (cf "Package-and-symbol/symbol-defclass.lisp")
    (cf "Arithmetic/number-defclass.lisp")
    (cf "Arithmetic/real-defclass.lisp")
    (cf "Arithmetic/rational-defclass.lisp")
    (cf "Arithmetic/integer-defclass.lisp")
    (cf "Arithmetic/fixnum-defclass.lisp")
    (cf "CLOS/specializer-direct-generic-functions-defgeneric.lisp")
    (cf "CLOS/setf-specializer-direct-generic-functions-defgeneric.lisp")
    (cf "CLOS/specializer-direct-methods-defgeneric.lisp")
    (cf "CLOS/setf-specializer-direct-methods-defgeneric.lisp")
    (cf "CLOS/eql-specializer-object-defgeneric.lisp")
    (cf "CLOS/unique-number-defgeneric.lisp")
    (cf "CLOS/class-name-defgeneric.lisp")
    (cf "CLOS/class-direct-subclasses-defgeneric.lisp")
    (cf "CLOS/setf-class-direct-subclasses-defgeneric.lisp")
    (cf "CLOS/class-direct-default-initargs-defgeneric.lisp")
    (cf "CLOS/documentation-defgeneric.lisp")
    (cf "CLOS/setf-documentation-defgeneric.lisp")
    (cf "CLOS/class-finalized-p-defgeneric.lisp")
    (cf "CLOS/setf-class-finalized-p-defgeneric.lisp")
    (cf "CLOS/class-precedence-list-defgeneric.lisp")
    (cf "CLOS/precedence-list-defgeneric.lisp")
    (cf "CLOS/setf-precedence-list-defgeneric.lisp")
    (cf "CLOS/instance-size-defgeneric.lisp")
    (cf "CLOS/setf-instance-size-defgeneric.lisp")
    (cf "CLOS/class-direct-slots-defgeneric.lisp")
    (cf "CLOS/class-direct-superclasses-defgeneric.lisp")
    (cf "CLOS/class-default-initargs-defgeneric.lisp")
    (cf "CLOS/setf-class-default-initargs-defgeneric.lisp")
    (cf "CLOS/class-slots-defgeneric.lisp")
    (cf "CLOS/setf-class-slots-defgeneric.lisp")
    (cf "CLOS/class-prototype-defgeneric.lisp")
    (cf "CLOS/setf-class-prototype-defgeneric.lisp")
    (cf "CLOS/entry-point-defgenerics.lisp")
    (cf "CLOS/environment-defgenerics.lisp")
    (cf "CLOS/dependents-defgeneric.lisp")
    (cf "CLOS/setf-dependents-defgeneric.lisp")
    (cf "CLOS/generic-function-name-defgeneric.lisp")
    (cf "CLOS/generic-function-lambda-list-defgeneric.lisp")
    (cf "CLOS/generic-function-argument-precedence-order-defgeneric.lisp")
    (cf "CLOS/generic-function-declarations-defgeneric.lisp")
    (cf "CLOS/generic-function-method-class-defgeneric.lisp")
    (cf "CLOS/generic-function-method-combination-defgeneric.lisp")
    (cf "CLOS/generic-function-methods-defgeneric.lisp")
    (cf "CLOS/setf-generic-function-methods-defgeneric.lisp")
    (cf "CLOS/initial-methods-defgeneric.lisp")
    (cf "CLOS/setf-initial-methods-defgeneric.lisp")
    (cf "CLOS/call-history-defgeneric.lisp")
    (cf "CLOS/setf-call-history-defgeneric.lisp")
    (cf "CLOS/specializer-profile-defgeneric.lisp")
    (cf "CLOS/setf-specializer-profile-defgeneric.lisp")
    (cf "CLOS/method-function-defgeneric.lisp")
    (cf "CLOS/method-generic-function-defgeneric.lisp")
    (cf "CLOS/setf-method-generic-function-defgeneric.lisp")
    (cf "CLOS/method-lambda-list-defgeneric.lisp")
    (cf "CLOS/method-specializers-defgeneric.lisp")
    (cf "CLOS/method-qualifiers-defgeneric.lisp")
    (cf "CLOS/accessor-method-slot-definition-defgeneric.lisp")
    (cf "CLOS/setf-accessor-method-slot-definition-defgeneric.lisp")
    (cf "CLOS/slot-definition-name-defgeneric.lisp")
    (cf "CLOS/slot-definition-allocation-defgeneric.lisp")
    (cf "CLOS/slot-definition-type-defgeneric.lisp")
    (cf "CLOS/slot-definition-initargs-defgeneric.lisp")
    (cf "CLOS/slot-definition-initform-defgeneric.lisp")
    (cf "CLOS/slot-definition-initfunction-defgeneric.lisp")
    (cf "CLOS/slot-definition-storage-defgeneric.lisp")
    (cf "CLOS/slot-definition-readers-defgeneric.lisp")
    (cf "CLOS/slot-definition-writers-defgeneric.lisp")
    (cf "CLOS/slot-definition-location-defgeneric.lisp")
    (cf "CLOS/setf-slot-definition-location-defgeneric.lisp")
    (cf "CLOS/variant-signature-defgeneric.lisp")
    (cf "CLOS/template-defgeneric.lisp")
    (cf "CLOS/make-method-for-generic-function.lisp")
    (cf "CLOS/ensure-method.lisp")
    (cf "CLOS/classp-defgeneric.lisp")
    (cf "CLOS/classp-defmethods.lisp")
    (cf "CLOS/class-unique-number-defparameter.lisp")
    (cf "Package-and-symbol/symbol-name-defgeneric.lisp")
    (cf "Package-and-symbol/symbol-package-defgeneric.lisp")
    ;; Files related to method combinations
    (cf "Method-combination/make-method-combination-defun.lisp")
    (cf "Method-combination/accessor-defgenerics.lisp")
    (cf "Method-combination/find-method-combination.lisp")
    (cf "Method-combination/method-combination-template-defclass.lisp")
    (cf "CLOS/standard-method-combination.lisp")
    (cf "CLOS/find-method-combination-defgenerics.lisp")
    (cf "CLOS/find-method-combination-defmethods.lisp")
    (cf "Method-combination/define-method-combination-defmacro.lisp")
    (cf "CLOS/sub-specializer-p.lisp")
    (cf "CLOS/compute-applicable-methods-support.lisp")
    (cf "CLOS/compute-applicable-methods-defgenerics.lisp")
    (cf "CLOS/compute-applicable-methods-defmethods.lisp")
    (cf "CLOS/compute-effective-method-defgenerics.lisp")
    (cf "CLOS/compute-effective-method-support.lisp")
    (cf "CLOS/compute-effective-method-defmethods.lisp")
    (cf "CLOS/no-applicable-method-defgenerics.lisp")
    (cf "CLOS/no-applicable-method.lisp")
    (cf "CLOS/compute-discriminating-function-defgenerics.lisp")
    (cf "CLOS/compute-discriminating-function-support.lisp")
    (cf "CLOS/compute-discriminating-function-support-c.lisp")
    (cf "CLOS/compute-discriminating-function-defmethods.lisp")
    (cf "CLOS/standard-instance-access.lisp")
    (cf "CLOS/invalidate-discriminating-function.lisp")
    (cf "CLOS/generic-function-initialization-support.lisp")
    (cf "CLOS/generic-function-initialization-defmethods.lisp")
    (cf "CLOS/add-remove-direct-subclass-support.lisp")
    (cf "CLOS/add-remove-direct-subclass-defgenerics.lisp")
    (cf "CLOS/add-remove-direct-subclass-defmethods.lisp")
    (cf "CLOS/add-remove-direct-method-defgenerics.lisp")
    (cf "CLOS/add-remove-direct-method-support.lisp")
    (cf "CLOS/add-remove-direct-method-defmethods.lisp")
    (cf "CLOS/add-remove-method-defgenerics.lisp")
    (cf "CLOS/add-remove-method-support.lisp")
    (cf "CLOS/add-remove-method-defmethods.lisp")
    (cf "CLOS/add-accessor-method.lisp")
    (cf "CLOS/validate-superclass-defgenerics.lisp")
    (cf "CLOS/validate-superclass-defmethods.lisp")
    (cf "CLOS/class-initialization-support.lisp")
    (cf "CLOS/class-initialization-defmethods.lisp")
    (cf "CLOS/effective-slot-definition-class-support.lisp")
    (cf "CLOS/effective-slot-definition-class-defgeneric.lisp")
    (cf "CLOS/effective-slot-definition-class-defmethods.lisp")
    (cf "CLOS/class-finalization-defgenerics.lisp")
    (cf "CLOS/class-finalization-support.lisp")
    (cf "CLOS/class-finalization-defmethods.lisp")
    (cf "CLOS/stamp-offset-defconstant.lisp")
    (cf "CLOS/allocate-instance-defgenerics.lisp")
    (cf "CLOS/allocate-instance-support.lisp")
    (cf "CLOS/allocate-instance-defmethods.lisp")
    (cf "CLOS/slot-bound-using-index.lisp")
    (cf "CLOS/slot-value-etc-defuns.lisp")
    (cf "CLOS/slot-value-etc-defgenerics.lisp")
    (cf "CLOS/slot-value-etc-support.lisp")
    (cf "CLOS/slot-value-etc-defmethods.lisp")
    (cf "CLOS/instance-slots-offset-defconstant.lisp")
    (cf "CLOS/shared-initialize-support.lisp")
    (cf "CLOS/shared-initialize-defgenerics.lisp")
    (cf "CLOS/shared-initialize-defmethods.lisp")
    (cf "CLOS/initialize-instance-support.lisp")
    (cf "CLOS/initialize-instance-defgenerics.lisp")
    (cf "CLOS/initialize-instance-defmethods.lisp")
    (cf "CLOS/make-instance-support.lisp")
    (cf "CLOS/default-superclasses-defgeneric.lisp")
    (cf "CLOS/default-superclasses-defmethods.lisp")
    (cf "CLOS/reinitialize-instance-defgenerics.lisp")
    (cf "CLOS/ensure-class-using-class-support.lisp")
    (cf "CLOS/ensure-class-using-class-defgenerics.lisp")
    (cf "CLOS/ensure-class-using-class-defmethods.lisp")
    (cf "CLOS/satiation.lisp")
    (cf "Evaluation-and-compilation/lambda.lisp")
    (cf "Data-and-control-flow/setf-defmacro.lisp")
    (cf "Data-and-control-flow/get-setf-expansion-defun.lisp")
    (cf "Data-and-control-flow/eq-defun.lisp")
    (cf "Data-and-control-flow/defun-defmacro.lisp")
    (cf "Data-and-control-flow/fdefinition-defun.lisp")
    (cf "Data-and-control-flow/setf-fdefinition-defun.lisp")
    (cf "Data-and-control-flow/fboundp-defun.lisp")
    (cf "Data-and-control-flow/fmakunbound-defun.lisp")
    (cf "Data-and-control-flow/functionp-defgeneric.lisp")
    (cf "Data-and-control-flow/functionp-defmethods.lisp")
    (cf "Data-and-control-flow/defconstant-defmacro.lisp")
    (cf "Data-and-control-flow/defparameter-defmacro.lisp")
    (cf "Data-and-control-flow/defvar-defmacro.lisp")
    (cf "Data-and-control-flow/return-defmacro.lisp")
    (cf "Data-and-control-flow/psetf-support.lisp")
    (cf "Data-and-control-flow/psetf-defmacro.lisp")
    (cf "Data-and-control-flow/psetq-defmacro.lisp")
    (cf "Data-and-control-flow/destructuring-bind-defmacro.lisp")
    (cf "Data-and-control-flow/rotatef-defmacro.lisp")
    (cf "Data-and-control-flow/shiftf-support.lisp")
    (cf "Data-and-control-flow/shiftf-defmacro.lisp")
    (cf "Data-and-control-flow/multiple-value-list-defmacro.lisp")
    (cf "Conditionals/macros.lisp")
    (cf "Character/character-defclass.lisp")
    (cf "Compiler/Code-object/generic-functions.lisp")
    (cf "Compiler/Code-object/code-object-defclass.lisp")))
