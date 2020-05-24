(cl:in-package #:sicl-boot-phase-7)

(defmethod sicl-genv:class-of
    ((object sicl-boot::header) environment)
  (slot-value object 'sicl-boot::%class))

(defun boot (boot)
  (with-accessors ((e3 sicl-boot:e3)
                   (e4 sicl-boot:e4)
                   (e5 sicl-boot:e5)
                   (e6 sicl-boot:e6))
      boot
    (load-source "CLOS/ensure-generic-function-using-class-support.lisp" e5)
    (load-source "CLOS/ensure-generic-function-using-class-defgenerics.lisp" e5)
    (load-source "CLOS/ensure-generic-function-using-class-defmethods.lisp" e5)
    (load-source "Cons/accessor-defuns.lisp" e5)
    (load-source "Arithmetic/plus-defun.lisp" e5)
    (load-source "Arithmetic/binary-plus-defgeneric.lisp" e5)
    (load-source "Arithmetic/binary-plus-defmethods.lisp" e5)
    (load-source "Cons/cxr.lisp" e5)
    (load-source "Cons/setf-cxr.lisp" e5)
    (load-source "Cons/getf-defun.lisp" e5)
    (load-printer e5)
    (load-make-instance e5)
    (load-source "CLOS/ensure-generic-function-defun.lisp" e5)
    (satiate-generic-functions e3 e4 e5)
    (patch-classes e4 e5)
    (patch-functions e3 e4 e5)
    (move-functions e5 e6)
    (setf (sicl-genv:fdefinition 'make-instance e5)
          (sicl-genv:fdefinition 'sicl-clos::make-instance-temp e5))
    (sicl-boot:import-functions-from-host
     '(cleavir-code-utilities:lambda-list-type-specifier
       sicl-genv:fdefinition)
     e5)
    (allocate-class-prototypes e5)
    (load-source "CLOS/defgeneric-support.lisp" e5)
    (load-source "CLOS/defgeneric-defmacro.lisp" e5)
    (load-source "CLOS/defmethod-support.lisp" e5)
    (load-source "CLOS/defmethod-defmacro.lisp" e5)
    (load-source "Conditionals/support.lisp" e5)
    (setf (sicl-genv:fdefinition 'proclaim e5)
          (lambda (&rest arguments)
            (format *trace-output* "args: ~s~%" arguments)))
    (load-source "Cons/member-if-not-defun.lisp" e5)
    (load-source "CLOS/defclass-support.lisp" e5)
    (load-source "CLOS/defclass-defmacro.lisp" e5)))
