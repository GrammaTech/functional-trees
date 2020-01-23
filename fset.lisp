(defpackage :functional-trees/fset
  (:nicknames :ft/fset)
  (:use cl :alexandria :iterate :functional-trees/core :fset)
  (:import-from :uiop/utility :nest)
  (:import-from :closer-mop :slot-definition-name :class-slots)
  (:shadow :map)
  (:shadowing-import-from :fset
                          :@
                          :unionf :appendf :with :removef
			  ;; Shadowed type/constructor names
			  :set
			  ;; Shadowed set operations
			  :union :intersection :set-difference :complement
			  ;; Shadowed sequence operations
			  :first :last :subseq :reverse :sort :stable-sort
			  :reduce
			  :find :find-if :find-if-not
			  :count :count-if :count-if-not
			  :position :position-if :position-if-not
			  :remove :remove-if :remove-if-not
			  :substitute :substitute-if :substitute-if-not
			  :some :every :notany :notevery)
  (:shadowing-import-from
   :cl :set :union :intersection :set-difference :complement)
  (:shadowing-import-from :alexandria :compose)
  (:export :fset-default-node-key :map :substitute-with)
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
    (iter (unless c (error "Path index too large"))
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

(defmethod splice ((tree node) (path list) (values t))
  (insert tree path (list values)))
(defmethod splice ((tree node) (path list) (values list))
  ;; Walk down the path creating new trees on the way up.
  (labels ((splice- (node path)
             (let ((index (car path)))
               (copy node
                     :children
                     (append (subseq (children node) 0 index)
                             (if (emptyp (cdr path))
                                 values
                                 (list (splice- (nth index (children node))
                                                (cdr path))))
                             (subseq (children node) index))))))
    (splice- tree path)))

(defmethod insert ((tree node) (path list) value)
  (splice tree path (list value)))

(defmethod size ((other t)) 0)
(defmethod size ((node node))
  (1+ (reduce #'+ (mapcar #'size (children node)))))


;;; Printing methods (rely on conversion functions).
(defmethod print-object ((obj node) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a" (convert 'list obj)))))

(defmethod print-object ((obj finger) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a ~a~@[ ~a~]"
                (node obj) (path obj) (residue obj)))))

(defmethod print-object ((obj path-transform) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a ~a"
                (transforms obj) (from obj)))))


;;; FSET conversion operations
(defmethod convert ((to-type (eql 'list)) (node node-with-data)
                    &key (value-fn #'data) &allow-other-keys)
  "Convert NODE of type node-with-data to a list using `data' as the value-fn."
  (call-next-method to-type node :value-fn value-fn))

(defmethod convert ((to-type (eql 'list)) (node node)
                    &key (value-fn nil value-fn-p) &allow-other-keys)
  "Convert NODE of type node to a list."
  (declare (optimize (speed 3)))
  (when value-fn-p (setf value-fn (coerce value-fn 'function)))
  (labels ((convert- (node)
             (declare (type function value-fn))
             (if (typep node 'node)
                 (cons (if value-fn-p (funcall value-fn node) node)
                       (mapcar #'convert- (children node)))
                 node)))
    (convert- node)))

(defmethod convert ((to-type (eql 'list)) (finger finger)
                    &key &allow-other-keys)
  (let ((cached (ft/core::cache finger)))
    (if (typep cached 'node)
        (convert to-type cached)
        cached)))

(defmethod convert ((to-type (eql 'alist)) (node node)
                    &key (value-fn nil value-fn-p) &allow-other-keys)
  (convert
   'list node :value-fn
   (if value-fn-p value-fn
       (let ((slots
              (nest
               (remove-if (rcurry #'member '(name transform finger children)))
               (mapcar #'slot-definition-name (class-slots (class-of node))))))
         (lambda (node)
           (apply #'append
                  (mapcar (lambda (slot)
                            (when-let ((val (slot-value node slot)))
                              (list (cons (make-keyword slot) val))))
                          slots)))))))

(defmethod convert ((to-type (eql 'node-with-data)) (sequence list) &key &allow-other-keys)
  (labels ((make-node (list-form)
             (if (consp list-form)
                 (make-instance 'node-with-data
                   :data (car list-form)
                   :children (mapcar #'make-node (cdr list-form)))
                 list-form)))
    (populate-fingers (make-node sequence))))


;;; FSET sequence operations (+ two) for functional tree.
(defgeneric fset-default-node-key (node-type element)
  (:documentation "Default key to use to process ELEMENT as possible NODE-TYPE.")
  (:method ((node-type t) (element t)) element)
  (:method ((node-type (eql 'node-with-data)) (element node-with-data)) (data element)))

(defgeneric map (result-type function first &rest more)
  (:documentation
   "If FIRST is a Lisp sequence, this simply calls `cl:map'.
On a functional tree the nodes of the tree are mapped.")
  (:method (result-type (function symbol) first &rest more)
    (apply #'map (coerce function 'function) first more))
  (:method (result-type function (first sequence) &rest more)
    (apply #'cl:map function first more))
  (:method (result-type function (first seq) &rest more &aux result)
    (when more (error "`ft:map' does not support mapping multiple trees."))
    (do-seq (element first :value (coerce (nreverse result) result-type))
      (push (funcall function element) result)))
  (:method (result-type function (first node) &rest more)
    (when more (error "`ft:map' does not support mapping multiple trees."))
    (labels ((map- (function subtree)
               (if (typep subtree 'node)
                   (make-instance 'node-with-data
                     :data (funcall function (data subtree))
                     :children (mapcar function (children subtree)))
                   (funcall function subtree))))
      (let ((result (map- function first)))
        (case result-type
          (node result)
          (otherwise (coerce (convert 'list result) result-type)))))))

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

(defmethod reduce (fn (node node) &rest rest &key &allow-other-keys)
  (apply #'reduce fn (flatten (convert 'list node)) rest))

(defmethod find (item (node node) &rest rest &key &allow-other-keys)
  (apply #'find item (flatten (convert 'list node)) rest))

(defmethod find-if (predicate (node node) &rest rest &key &allow-other-keys)
  (apply #'find-if predicate (flatten (convert 'list node)) rest))

(defmethod find-if-not (predicate (node node) &rest rest &key &allow-other-keys)
  (apply #'find-if-not predicate (flatten (convert 'list node)) rest))

(defmethod count (item (node node) &rest rest &key &allow-other-keys)
  (apply #'count item (flatten (convert 'list node)) rest))

(defmethod count-if (predicate (node node) &rest rest &key &allow-other-keys)
  (apply #'count-if predicate (flatten (convert 'list node)) rest))

(defmethod count-if-not (predicate (node node) &rest rest &key &allow-other-keys)
  (apply #'count-if-not predicate (flatten (convert 'list node)) rest))

(defmethod position (item (node node) &key
                                        (test #'equalp)
                                        (key (curry #'fset-default-node-key (type-of node)) key-p)
                                        &allow-other-keys)
  (apply #'position-if (curry (coerce test 'function) item) node
         (when key-p (list :key key))))

(defmethod position-if (predicate (node node)
                        &key from-end end start test-not test
                          (key (curry #'fset-default-node-key (type-of node))))
  (assert (notany #'identity from-end end start test-not test)
          (from-end end start test-not test)
          "TODO: implement support for ~a key in `position-if'"
          (cdr (find-if #'car
                        (mapcar #'cons
                                (list from-end end start test-not test)
                                '(from-end end start test-not test)))))
  (when key (setf key (coerce key 'function)))
  (labels ((check (item) (funcall predicate (if key (funcall key item) item)))
           (position- (predicate node path)
             (if (typep node 'node)
                 (if (check node)
                     (return-from position-if (nreverse path))
                     (mapcar (lambda (child index)
                               (position- predicate child (cons index path)))
                             (children node)
                             (iota (length (children node)))))
                 (when (check node)
                   (return-from position-if (nreverse path))))))
    (position- (coerce predicate 'function) node nil)
    nil))

(defmethod position-if-not (predicate (node node)
                            &key (key (curry #'fset-default-node-key (type-of node)) key-p)
                              &allow-other-keys)
  (apply #'position-if (complement predicate) node (when key-p (list :key key))))

(defmethod remove (item (node node) &key (test #'equalp)
                                      (key (curry #'fset-default-node-key (type-of node)) key-p)
                                      &allow-other-keys)
  (apply #'remove-if (curry (coerce test 'function) item) node (when key-p (list :key key))))

(defmethod remove-if (predicate (node node)
                      &key (key (curry #'fset-default-node-key (type-of node)))
                        &allow-other-keys)
  (when key (setf key (coerce key 'function)))
  (labels
      ((check (node)
         (funcall predicate (if key (funcall (the function key) node) node)))
       (remove- (predicate node)
         (if (typep node 'node)
             (if (check node)
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
             (if (check node)
                 (values nil t)
                 (values (list node) nil)))))
    (car (remove- (coerce predicate 'function) node))))

(defmethod remove-if-not (predicate (node node)
                          &key (key (curry #'fset-default-node-key (type-of node)) key-p)
                            &allow-other-keys)
  (apply #'remove-if (complement predicate) node (when key-p (list :key key))))

(defmethod substitute
    (newitem olditem (node node) &key (test #'equalp)
                                   (key (curry #'fset-default-node-key (type-of node)) key-p)
                                   &allow-other-keys)
  (apply #'substitute-if newitem (curry (coerce test 'function) olditem) node
         :test test (when key-p (list :key key))))

(defmethod substitute-if (newitem predicate (node node)
                          &key (copy nil copyp)
                            (key (curry #'fset-default-node-key (type-of node)) key-p)
                            &allow-other-keys)
  (when copyp (setf copy (coerce copy 'function)))
  (setf predicate (coerce predicate 'function))
  (apply #'substitute-with
         (lambda (item)
           (when (funcall predicate item)
             (values (if copyp (funcall copy newitem) newitem) t)))
         node (when key-p (list :key key))))

(defmethod substitute-if-not (newitem predicate (node node)
                              &key (key (curry #'fset-default-node-key (type-of node)) key-p)
                                &allow-other-keys)
  (apply #'substitute-if newitem (complement predicate) node (when key-p (list :key key))))

(defmethod substitute-with (function (node node)
                            &key (key (curry #'fset-default-node-key (type-of node)))
                              &allow-other-keys)
  (when key (setf key (coerce key 'function)))
  (labels
      ((check (node)
         (funcall function (if key (funcall (the function key) node) node)))
       (substitute- (predicate node)
         (if (typep node 'node)
             (multiple-value-bind (value force) (check node)
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
             (multiple-value-bind (value force) (check node)
               (if (or force value)
                   (values (list value) t)
                   (values (list node) nil))))))
    (car (substitute- (coerce function 'function) node))))
