(cl:in-package #:sicl-string)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Utilities

;;; Generate a random string of length between MIN-LENGTH and
;;; MAX-LENGTH containing characters with codes between MIN-CODE and
;;; MAX-CODE.
(defun random-string (min-length max-length min-code max-code)
  (let* ((length (+ min-length (random (1+ (- max-length min-length)))))
	 (result (make-string length)))
    ;; Fill the string with some random characters.
    (loop for i from 0 below length
	  for code = (+ min-code (random (1+ (- max-code min-code))))
	  for char = (code-char code)
	  do (setf (char result i) char))
    result))

;;; Convert a string to a non-simple string (provided that strings
;;; with fill pointers are not simple on the host platform).
(defun string-to-non-simple-string (string)
  (make-array (length string)
	      :element-type 'character
	      :initial-contents (coerce string 'list)
	      :fill-pointer (length string)))

;;; Convert a string to a simple vector.
(defun string-to-simple-vector (string)
  (make-array (length string)
	      :initial-contents (coerce string 'list)))

;;; Convert s string to a non-simple vector (provided that strings
;;; with fill pointers are not simple on the host platform).
(defun string-to-non-simple-vector (string)	      
  (make-array (length string)
	      :initial-contents (coerce string 'list)
	      :fill-pointer (length string)))

;;; Return two random valid bounding indices for SEQUENCE.
(defun random-bounding-indices (sequence)
  (let* ((length (length sequence))
	 (start (random (1+ length)))
	 (end (+ start (random (1+ (- length start))))))
    (values start end)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Test NSTRING-UPCASE

(defun nlist-upcase (list start end)
  (loop for rest on list
	for i from 0
	when (and (<= start i) (< i end))
	  do (setf (car rest) (char-upcase (car rest))))
  list)

(defun test-one-nstring-upcase (string &key (start 0) end)
  (let ((list1 (coerce string 'list))
	(result (nstring-upcase string :start start :end end)))
    (let ((list2 (coerce result 'list)))
      (assert (eq result string))
      (let ((real-end (if (null end) (length list2) end)))
	(assert (equal (nlist-upcase list1 start real-end) list2))))))

(defun test-nstring-upcase (n)
  (loop repeat n
	do (let* ((string (random-string 0 10 0 500))
		  (length (length string))
		  (start (random (1+ length)))
		  (end (+ start (random (1+ (- length start))))))
	     (test-one-nstring-upcase string :start start :end end))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Test NSTRING-DOWNCASE

(defun nlist-downcase (list start end)
  (loop for rest on list
	for i from 0
	when (and (<= start i) (< i end))
	  do (setf (car rest) (char-downcase (car rest))))
  list)
  
(defun test-one-nstring-downcase (string &key (start 0) end)
  (let ((list1 (coerce string 'list))
	(result (nstring-downcase string :start start :end end)))
    (let ((list2 (coerce result 'list)))
      (assert (eq result string))
      (let ((real-end (if (null end) (length list2) end)))
	(assert (equal (nlist-downcase list1 start real-end) list2))))))

(defun test-nstring-downcase (n)
  (loop repeat n
	do (let* ((string (random-string 0 10 0 500))
		  (length (length string))
		  (start (random (1+ length)))
		  (end (+ start (random (1+ (- length start))))))
	     (test-one-nstring-downcase string :start start :end end))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Test NSTRING-CAPITALIZE

(defun nlist-capitalize (list start end)
  (loop with prev = #\Space
	for rest on list
	for i from 0
	when (and (<= start i) (< i end))
	  do (if (alphanumericp prev)
		 (setf (car rest) (char-downcase (car rest)))
		 (setf (car rest) (char-upcase (car rest))))
	     (setf prev (car rest)))
  list)

(defun test-one-nstring-capitalize (string &key (start 0) end)
  (let ((list1 (coerce string 'list))
	(result (nstring-capitalize string :start start :end end)))
    (let ((list2 (coerce result 'list)))
      (assert (eq result string))
      (let ((real-end (if (null end) (length list2) end)))
	(assert (equal (nlist-capitalize list1 start real-end) list2))))))

(defun test-nstring-capitalize (n)
  (loop repeat n
	do (let* ((string (random-string 0 10 0 500))
		  (length (length string))
		  (start (random (1+ length)))
		  (end (+ start (random (1+ (- length start))))))
	     (test-one-nstring-capitalize string :start start :end end))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Test STRING-LEFT-TRIM

(defun list-left-trim (chars list)
  (loop while (and (consp list) (member (car list) chars))
	do (pop list))
  list)

(defun test-one-string-left-trim (bag string)
  (let ((list-bag (coerce bag 'list))
	(list-string (coerce string 'list)))
    (assert (equal (list-left-trim list-bag list-string)
		   (coerce (string-left-trim bag string) 'list)))))

(defun test-string-left-trim (n)
  (loop repeat n
	do (let ((string (random-string 0 10 60 100))
		 (bag (random-string 0 5 60 150)))
	     (test-one-string-left-trim
	      bag
	      string)
	     (test-one-string-left-trim
	      bag
	      (string-to-non-simple-string string))
	     (test-one-string-left-trim
	      (string-to-non-simple-string bag)
	      string)
	     (test-one-string-left-trim
	      (string-to-non-simple-string bag)
	      (string-to-non-simple-string string))
	     (test-one-string-left-trim
	      (coerce bag 'list)
	      string)
	     (test-one-string-left-trim
	      (coerce bag 'list)
	      (string-to-non-simple-string string))
	     (test-one-string-left-trim
	      (string-to-simple-vector bag)
	      string)
	     (test-one-string-left-trim
	      (string-to-simple-vector bag)
	      (string-to-non-simple-string string))
	     (test-one-string-left-trim
	      (string-to-non-simple-vector bag)
	      string)
	     (test-one-string-left-trim
	      (string-to-non-simple-vector bag)
	      (string-to-non-simple-string string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Test STRING-RIGHT-TRIM

(defun list-right-trim (chars list)
  (reverse (list-left-trim chars (reverse list))))

(defun test-one-string-right-trim (bag string)
  (let ((list-bag (coerce bag 'list))
	(list-string (coerce string 'list)))
    (assert (equal (list-right-trim list-bag list-string)
		   (coerce (string-right-trim bag string) 'list)))))

(defun test-string-right-trim (n)
  (loop repeat n
	do (let ((string (random-string 0 10 60 100))
		 (bag (random-string 0 5 60 150)))
	     (test-one-string-right-trim
	      bag
	      string)
	     (test-one-string-right-trim
	      bag
	      (string-to-non-simple-string string))
	     (test-one-string-right-trim
	      (string-to-non-simple-string bag)
	      string)
	     (test-one-string-right-trim
	      (string-to-non-simple-string bag)
	      (string-to-non-simple-string string))
	     (test-one-string-right-trim
	      (coerce bag 'list)
	      string)
	     (test-one-string-right-trim
	      (coerce bag 'list)
	      (string-to-non-simple-string string))
	     (test-one-string-right-trim
	      (string-to-simple-vector bag)
	      string)
	     (test-one-string-right-trim
	      (string-to-simple-vector bag)
	      (string-to-non-simple-string string))
	     (test-one-string-right-trim
	      (string-to-non-simple-vector bag)
	      string)
	     (test-one-string-right-trim
	      (string-to-non-simple-vector bag)
	      (string-to-non-simple-string string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Test STRING-TRIM

(defun list-trim (chars list)
  (list-right-trim chars (list-left-trim chars list)))

(defun test-one-string-trim (bag string)
  (let ((list-bag (coerce bag 'list))
	(list-string (coerce string 'list)))
    (assert (equal (list-trim list-bag list-string)
		   (coerce (string-trim bag string) 'list)))))

(defun test-string-trim (n)
  (loop repeat n
	do (let ((string (random-string 0 10 60 100))
		 (bag (random-string 0 5 60 150)))
	     (test-one-string-trim
	      bag
	      string)
	     (test-one-string-trim
	      bag
	      (string-to-non-simple-string string))
	     (test-one-string-trim
	      (string-to-non-simple-string bag)
	      string)
	     (test-one-string-trim
	      (string-to-non-simple-string bag)
	      (string-to-non-simple-string string))
	     (test-one-string-trim
	      (coerce bag 'list)
	      string)
	     (test-one-string-trim
	      (coerce bag 'list)
	      (string-to-non-simple-string string))
	     (test-one-string-trim
	      (string-to-simple-vector bag)
	      string)
	     (test-one-string-trim
	      (string-to-simple-vector bag)
	      (string-to-non-simple-string string))
	     (test-one-string-trim
	      (string-to-non-simple-vector bag)
	      string)
	     (test-one-string-trim
	      (string-to-non-simple-vector bag)
	      (string-to-non-simple-string string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Test STRING=.

(defun list= (list1 list2 start1 end1 start2 end2)
  (let ((l1 (loop for i from 0
		  for c in list1
		  when (and (>= i start1) (< i end1))
		    collect c))
	(l2 (loop for i from 0
		  for c in list2
		  when (and (>= i start2) (< i end2))
		    collect c)))
    (and (= (length l1) (length l2))
	 (loop for c1 in l1
	       for c2 in l2
	       unless (char= c1 c2)
		 return nil
	       finally (return t)))))

(defun test-one-string=
    (string1 string2 &rest args &key (start1 0) end1 (start2 0) end2)
  (let ((e1 (if (null end1) (length string1) end1))
	(e2 (if (null end2) (length string2) end2)))
    (assert (eq (apply #'string= string1 string2 args)
		(list= (coerce string1 'list) (coerce string2 'list)
		       start1 e1 start2 e2)))))

(defun test-string= (n)
  (loop repeat n
	do (let ((string1 (random-string 0 5 64 66))
		 (string2 (random-string 0 5 64 66)))
	     (multiple-value-bind (start1 end1)
		 (random-bounding-indices string1)
	       (multiple-value-bind (start2 end2)
		   (random-bounding-indices string2)
		 (test-one-string=
		  string1
		  string2
		  :start1 start1 :start2 start2 :end1 end1 :end2 end2)
		 (test-one-string=
		  (string-to-non-simple-string string1)
		  string2
		  :start1 start1 :start2 start2 :end1 end1 :end2 end2)
		 (test-one-string=
		  string1
		  (string-to-non-simple-string string2)
		  :start1 start1 :start2 start2 :end1 end1 :end2 end2)
		 (test-one-string=
		  (string-capitalize string1)
		  string2
		  :start1 start1 :start2 start2 :end1 end1 :end2 end2))))))
