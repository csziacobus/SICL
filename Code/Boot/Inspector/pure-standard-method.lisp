(cl:in-package #:sicl-boot-inspector)

(defmethod clouseau:inspect-object-using-state
    ((object t)
     (state  inspected-pure-standard-method)
     (style  (eql :collapsed))
     (stream t))
  (clim:with-drawing-options (stream :ink clim:+blue+)
    (format stream
            "Pure standard method")))

(defmethod clouseau:inspect-object-using-state
    ((object t)
     (state  inspected-pure-standard-method)
     (style  (eql :expanded-header))
     (stream t))
  (clim:with-drawing-options (stream :ink clim:+blue+)
    (format stream "Pure standard method")))

(defmethod clouseau:inspect-object-using-state
    ((object t)
     (state  inspected-pure-standard-method)
     (style  (eql :expanded-body))
     (stream t))
  (let ((e5 (sicl-boot::e5 *boot*)))
    (declare (ignore e5))
    (clouseau:with-preserved-cursor-x (stream)
      (clim:formatting-table (stream)
        (clouseau:format-place-row
         stream
         object
         'clouseau:pseudo-place
         (class-of-object object)
         :label "Class")
        (clouseau:format-place-row
         stream
         object
         'clouseau:pseudo-place
         (aref (rack-of-object object) 0)
         :label "Stamp")
        (present-pure-object-slots object stream)))))
