(cl:in-package #:asdf-user)

(defsystem :cleavir-mir
  :depends-on (:cleavir-ir)
  :serial t
  :components
  ((:file "utilities")
   (:file "general")
   (:file "conditions")
   (:file "graphviz-drawing")))
