(defpackage :functional-trees/fset
  (:nicknames :ft/fset)
  (:use cl :alexandria :iterate :functional-trees :fset)
  (:shadowing-import-from :fset
			  ;; Shadowed set operations
			  #:union #:intersection #:set-difference #:complement
			  ;; Shadowed sequence operations
			  #:first #:last #:subseq #:reverse #:sort #:stable-sort
			  #:reduce
			  #:find #:find-if #:find-if-not
			  #:count #:count-if #:count-if-not
			  #:position #:position-if #:position-if-not
			  #:remove #:remove-if #:remove-if-not
			  #:substitute #:substitute-if #:substitute-if-not
			  #:some #:every #:notany #:notevery
                          ;; Shadowed from Alexandria
                          #:compose #:unionf #:appendf #:removef)
  (:shadowing-import-from :cl :set :map)
  (:shadowing-import-from :iterate :with)
  (:documentation "FSET Integration for functional-trees."))
(in-package :functional-trees/fset)


;;; Useful replacement function, not specific to FT or FSET.
(defgeneric substitute-with (predicate sequence)
  (:documentation
   "Substitute elements of SEQUENCE with result of PREDICATE when non-nil.
If secondary return value of PREDICATE is non-nil force substitution
  with primary value even if it is nil.")
  (:method (predicate (sequence sequence))
    (let ((predicate (coerce predicate 'function)))
      (map (type-of sequence)
           (lambda (element)
             (multiple-value-bind (value force)
                 (funcall predicate element)
               (if force value (or value element))))
           sequence)))
  (:method (predicate (seq seq) &aux result)
    (let ((predicate (coerce predicate 'function)))
      (do-seq (element seq)
        (multiple-value-bind (value force)
            (funcall predicate element)
          (push (if force value (or value element)) result)))
      (convert 'seq (nreverse result)))))


;;; Relevant FSET operations for functional tree.
(defmethod reduce (fn (node node) &rest rest &key &allow-other-keys)
  (apply #'reduce fn (flatten (to-list node)) rest))

(defmethod find (item (node node) &rest rest &key &allow-other-keys)
  (apply #'find item (flatten (to-list node)) rest))

(defmethod find-if (predicate (node node) &rest rest &key &allow-other-keys)
  (apply #'find-if predicate (flatten (to-list node)) rest))

(defmethod find-if-not (predicate (node node) &rest rest &key &allow-other-keys)
  (apply #'find-if-not predicate (flatten (to-list node)) rest))

(defmethod count (item (node node) &rest rest &key &allow-other-keys)
  (apply #'count item (flatten (to-list node)) rest))

(defmethod count-if (predicate (node node) &rest rest &key &allow-other-keys)
  (apply #'count-if predicate (flatten (to-list node)) rest))

(defmethod count-if-not (predicate (node node) &rest rest &key &allow-other-keys)
  (apply #'count-if-not predicate (flatten (to-list node)) rest))

(defmethod position (item (node node) &key (test #'equalp) &allow-other-keys)
  (position-if (curry (coerce test 'function) item) node))

(defmethod position-if (predicate (node node) &key &allow-other-keys)
  (labels ((position- (predicate node path)
             (if (typep node 'node)
                 (if (funcall predicate (data node))
                     (return-from position-if (nreverse path))
                     (mapcar (lambda (child index)
                               (position- predicate child (cons index path)))
                             (children node)
                             (iota (length (children node)))))
                 (when (funcall predicate node)
                   (return-from position-if (nreverse path))))))
    (position- (coerce predicate 'function) node nil)))

(defmethod position-if-not (predicate (node node) &key &allow-other-keys)
  (position-if (cl:complement predicate) node))

(defmethod remove (item (node node) &key (test #'equalp) &allow-other-keys)
  (remove-if (curry (coerce test 'function) item) node))

(defmethod remove-if (predicate (node node) &key &allow-other-keys)
  (labels
      ((remove- (predicate node)
         (if (typep node 'node)
             (if (funcall predicate (data node))
                 (values nil t)
                 (let* ((modifiedp nil)
                        (new-children
                         (mappend
                          (lambda (child)
                            (multiple-value-bind (new was-modified-p)
                                (remove- predicate child)
                              (when was-modified-p (setf modifiedp t))
                              new))
                          (children node))))
                   (if (not modifiedp)
                       (values (list node) nil)
                       (values (list (copy node :children new-children)) t))))
             (if (funcall predicate node)
                 (values nil t)
                 (values (list node) nil)))))
    (car (remove- (coerce predicate 'function) node))))
