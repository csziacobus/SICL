(cl:in-package #:sicl-sequence)

(defmethod make-sequence-reader ((list list) start end from-end terminate)
  (declare (method-properties inlineable))
  (declare (function terminate))
  (multiple-value-bind (start end)
      (canonicalize-start-and-end list start end)
    (values
     (if (not from-end)
         ;; Forward iteration.
         (let ((current (nthcdr start list))
               (index start))
           (declare (array-index index))
           (lambda ()
             (if (= index end)
                 (funcall terminate)
                 (prog1 (pop current)
                   (incf index)))))
         ;; Backward iteration.
         (let ((index (1- end))
               (current '()))
           (declare (array-length index))
           (loop repeat (- end start)
                 for element in (nthcdr start list)
                 do (push element current))
           (lambda ()
             (if (= index start)
                 (funcall terminate)
                 (prog1 (pop current)
                   (decf index))))))
     (- end start))))

(seal-domain #'make-sequence-reader '(list t t t t))

(replicate-for-each-vector-class #1=#:vector-class
  (defmethod make-sequence-reader ((vector #1#) start end from-end terminate)
    (declare (method-properties inlineable))
    (declare (function terminate))
    (declare (type #1# vector))
    (multiple-value-bind (start end)
        (canonicalize-start-and-end vector start end)
      (values
       (if (not from-end)
           ;; Forward iteration.
           (let ((index start))
             (declare (array-length index))
             (lambda ()
               (if (= index end)
                   (funcall terminate)
                   (prog1 (elt vector index)
                     (incf index)))))
           ;; Backward iteration.
           (let ((index (1- end)))
             (declare (array-length index))
             (lambda ()
               (if (= index start)
                   (funcall terminate)
                   (prog1 (elt vector index)
                     (decf index))))))
       (- end start)))))

(seal-domain #'make-sequence-reader '(vector t t t t))
