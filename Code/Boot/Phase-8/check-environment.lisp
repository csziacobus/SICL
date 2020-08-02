(cl:in-package #:sicl-boot-phase-8)

(defun find-class-name (class environment)
  (do-all-symbols (symbol nil)
    (when (eq (sicl-genv:find-class symbol environment) class)
      (return-from find-class-name symbol))))

(defun check-effective-slot-definition (effective-slot-definition environment)
  (if (not (typep effective-slot-definition 'sicl-boot::header))
      (format *trace-output* "    Effectiveq slot definition is not a SICL object.~%")
      (progn 
        (let ((class (slot-value effective-slot-definition 'sicl-boot::%class)))
          (if (not (typep class 'sicl-boot::header))
              (format *trace-output* "    Class of effective slot definition is not a SICL object.~%")
              (let ((class-name (find-class-name class environment)))
                (when (null class-name)
                  (format *trace-output* "   Class of effective slot definition is not in environment.~%"))))))))

(defun check-effective-slot-definitions (effective-slot-definitions environment)
  (loop for effective-slot-definition in effective-slot-definitions
        do (check-effective-slot-definition effective-slot-definition environment)))

(defun check-class (name class environment)
  (format *trace-output* "Checking class named ~s~%" name)
  (if (not (typep class 'sicl-boot::header))
      (format *trace-output* "    Class named ~s is not a SICL object.~%" name)
      (progn 
        (let ((metaclass (slot-value class 'sicl-boot::%class)))
          (if (not (typep metaclass 'sicl-boot::header))
              (format *trace-output* "    Metaclass is not a SICL object.~%")
              (let ((metaclass-name (find-class-name metaclass environment)))
                (when (null metaclass-name)
                  (format *trace-output* "   Metaclass is not a class in environment.~%")))))
        (let ((rack (slot-value class 'sicl-boot::%rack)))
          (check-effective-slot-definitions (aref rack 1) environment)))))

(defun check-classes (environment)
  (let ((table (make-hash-table :test #'eq)))
    (do-all-symbols (symbol)
      (unless (gethash symbol table)
        (setf (gethash symbol table) t)
        (let ((potential-class (sicl-genv:find-class symbol environment)))
          (unless (null potential-class)
            (check-class symbol potential-class environment)))))))
        