(defpackage :functional-trees/fset
  (:nicknames :ft/fset)
  (:use cl :alexandria :iterate :functional-trees :fset)
  (:shadowing-import-from :fset
                          :@
                          :compose :unionf :appendf :with :removef
			  ;; Shadowed type/constructor names
			  #:set #:map
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
			  #:some #:every #:notany #:notevery)
  (:shadowing-import-from
   :cl :set :map :union :intersection :set-difference :complement)
  (:documentation "FSET Integration for functional-trees."))
(in-package :functional-trees/fset)


;;; Define `lookup' methods to work with FSet's `@' macro.
(defmethod lookup ((node t) (path null)) node)
(defmethod lookup ((node node) (path cons))
  (lookup (lookup node (car path)) (cdr path)))
(defmethod lookup ((node node) (finger finger))
    (let ((new-finger (transform-finger finger node)))
      (values (lookup node (path new-finger)) (residue new-finger))))
(defmethod lookup ((node node) (i integer))
  ;; Replace this with (@ (children node) i)?
  (unless (typep i '(integer 0))
        (error "Not a valid path index: ~a" i))
  (let* ((c (children node)))
    (iter (unless c (error "Path index too large: ~a (must be < ~a)"
                           (car path) (- (car path) i)))
          (while (> i 0))
          (pop c)
          (decf i))
    (car c)))

(defmethod with ((tree node) path &optional (value nil valuep))
  "Adds VALUE (value2) at PATH (value1) in TREE."
  (fset::check-three-arguments valuep 'with 'node)
  ;; Walk down the path creating new trees on the way up.
  (labels ((with- (node path)
             (if (emptyp path)
                 value
                 (let ((index (car path)))
                   (copy node
                         :children
                         (append (subseq (children node) 0 index)
                                 (list (with- (nth index (children node)) (cdr path)))
                                 (subseq (children node) (1+ index))))))))
    (with- tree path)))

(defmethod less (tree path &optional (arg2 nil arg2p))
  (declare (ignore arg2))
  (fset::check-two-arguments arg2p 'less 'node)
  (labels ((less- (node path)
             (let ((index (car path)))
               (copy node
                     :children
                     (append (subseq (children node) 0 index)
                             (unless (emptyp (cdr path))
                               (list (less- (nth index (children node)) (cdr path))))
                             (subseq (children node) (1+ index)))))))
    (less- tree path)))

(defmethod size ((other t)) 0)
(defmethod size ((node node))
  (1+ (reduce #'+ (mapcar #'size (children node)))))


;;; Useful replacement function, not specific to FT or FSET.
(defgeneric substitute-with (predicate sequence &key &allow-other-keys)
  (:documentation
   "Substitute elements of SEQUENCE with result of PREDICATE when non-nil.
If secondary return value of PREDICATE is non-nil force substitution
  with primary value even if it is nil.")
  (:method (predicate (sequence sequence) &key &allow-other-keys )
    (let ((predicate (coerce predicate 'function)))
      (map (type-of sequence)
           (lambda (element)
             (multiple-value-bind (value force)
                 (funcall predicate element)
               (if force value (or value element))))
           sequence)))
  (:method (predicate (seq seq) &key &allow-other-keys &aux result)
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
    (position- (coerce predicate 'function) node nil)
    nil))

(defmethod position-if-not (predicate (node node) &key &allow-other-keys)
  (position-if (complement predicate) node))

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

(defmethod remove-if-not (predicate (node node) &key &allow-other-keys)
  (remove-if (complement predicate) node))

(defmethod substitute
    (newitem olditem (node node) &key (test #'equalp) &allow-other-keys)
  (substitute-if newitem (curry (coerce test 'function) olditem) node))

(defmethod substitute-if (newitem predicate (node node) &key (copy nil copyp) &allow-other-keys)
  (when copyp (setf copy (coerce copy 'function)))
  (setf predicate (coerce predicate 'function))
  (substitute-with (lambda (item)
                     (when (funcall predicate item)
                       (values (if copyp (funcall copy newitem) newitem) t)))
                   node))

(defmethod substitute-if-not (newitem predicate (node node) &key &allow-other-keys)
  (substitute-if newitem (complement predicate) node))

(defmethod substitute-with (function (node node) &key &allow-other-keys)
  (labels
      ((substitute- (predicate node)
         (if (typep node 'node)
             (multiple-value-bind (value force)
                 (funcall function (data node))
               (if (or force value)
                   (values (list value) t)
                   (let* ((modifiedp nil)
                          (new-children
                           (mappend
                            (lambda (child)
                              (multiple-value-bind (new was-modified-p)
                                  (substitute- predicate child)
                                (when was-modified-p (setf modifiedp t))
                                new))
                            (children node))))
                     (if (not modifiedp)
                         (values (list node) nil)
                         (values (list (copy node :children new-children)) t)))))
             (multiple-value-bind (value force)
                 (funcall function node)
               (if (or force value)
                   (values (list value) t)
                   (values (list node) nil))))))
    (car (substitute- (coerce function 'function) node))))
