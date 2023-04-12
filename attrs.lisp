(defpackage :functional-trees/attrs
  (:nicknames :ft/attrs)
  (:use
   :common-lisp :alexandria :iterate
   :functional-trees/functional-trees
   :curry-compose-reader-macros
   :named-readtables)
  (:shadowing-import-from :trivial-garbage :make-weak-hash-table)
  (:shadowing-import-from :fset :subst :subst-if :subst-if-not :mapcar :mapc)
  (:import-from :serapeum :standard/context)
  (:export
   :def-attr-fun
   :with-attr-table
   :*attrs*
   :attrs-root*
   :mapc-attrs
   :mapc-attrs-children
   :mapc-attrs-slot
   :attr-missing
   :attrs-table
   :attrs-root
   :attr-proxy
   :attrs-invalid
   :prune-attrs
   :has-attributes-p
   :has-attribute-p))

(in-package :functional-trees/attrs)
(in-readtable :curry-compose-reader-macros)

;;; Attributes are stored in a hash table mapping
;;; nodes to list of values.

(defstruct attrs
  (table (make-attr-table))
  (proxies (make-attr-table))
  (root  nil)
  (previous nil))

(declaim (special *attrs*))

(defun make-attr-table (&rest args)
  (multiple-value-call #'make-weak-hash-table
    :weakness :key
    :test #'eq
    (values-list args)))

(defun attrs-root* ()
  "Get the root of the current attrs table."
  (attrs-root *attrs*))

(defun attr-proxy (attr)
  (gethash attr (attrs-proxies *attrs*)))

(defun (setf attr-proxy) (value attr)
  (setf (gethash attr (attrs-proxies *attrs*))
        value))

(defun attrs-tables (attrs)
  "Return list of tables from dynamically active attrs."
  (loop for ats = attrs then (attrs-previous ats)
        while ats
        collect (attrs-table ats)))

(defgeneric prune-attrs (root)
  (:method-combination standard/context)
  (:documentation "Hook to prune attributes.")
  (:method ((root t))))

(defun call/attr-table (root fn)
  "Invoke FN with an attrs instance for ROOT.
ROOT might be an attrs instance itself.

If the active attrs instance has ROOT for its root, it is not
replaced."
  (multiple-value-bind (*attrs* new)
      (cond
        ((typep root 'attrs) root)
        ((and (boundp '*attrs*)
              (eql (attrs-root *attrs*)
                   root))
         *attrs*)
        (t
         (values
          (make-attrs :root root
                      :previous
                      (and (boundp '*attrs*)
                           (symbol-value '*attrs*)))
          t)))
    (when new
      (prune-attrs root))
    (funcall fn)))

(defmacro with-attr-table (root &body body)
  "Create an ATTRS structure with root ROOT
   and bind it to *ATTRS*, then evaluate BODY
   in an implicit PROGN.  If ROOT is an ATTRS
   structure, simply bind *ATTRS* to it."
  (with-gensyms (attr-table-fn)
    `(flet ((,attr-table-fn () ,@body))
       (declare (dynamic-extent #',attr-table-fn))
       (call/attr-table ,root #',attr-table-fn))))

(defmacro def-attr-fun (name (&rest optional-args) &body methods)
  (assert (symbolp name))
  (assert (every #'symbolp optional-args))
  (with-gensyms (node fn present?)
    (let ((docstring
            (when (stringp (car methods))
              (pop methods)))
          (body
            `(flet ((,fn () (call-next-method)))
               (declare (dynamic-extent #',fn))
               (memoize-attr-fun ,node ',name #',fn))))
      `(defgeneric ,name (,node ,@(when optional-args `(&optional ,@optional-args)))
         ,@(when docstring `((:documentation ,docstring)))
         (:method-combination standard/context)
         (:method :context (,node ,@(when optional-args
                                      `(&optional (,(car optional-args) nil ,present?)
                                                  ,@(cdr optional-args))))
           ,@(when optional-args
               `((declare (ignorable ,@optional-args))))
           ,(if optional-args
                `(if ,present?
                     ,body
                     (cached-attr-fn ,node ',name))
                body))
         ,@methods))))

(defun has-attributes-p (node &aux (tables (attrs-tables *attrs*)))
  (loop for table in tables
        thereis (nth-value 1 (gethash node table))))

(defun has-attribute-p (node fn-name &aux (tables (attrs-tables *attrs*)))
  (loop for table in tables
        thereis (assoc fn-name (gethash node table))))

(defun retrieve-memoized-attr-fn (node fn-name tables)
  "Look up memoized value for FN-NAME on NODE.
Return the node's alist, and the pair for FN-NAME if the alist has
one."
  (flet ((scan-alist (alist)
           (iter (for p in alist)
                 (when (eql (car p) fn-name)
                   (etypecase (cdr p)
                     ;; Return the match. This should not be written
                     ;; to.
                     (list (return-from retrieve-memoized-attr-fn (values alist p)))
                     (t
                      (assert (eql (cdr p) :in-progress))
                      (error "Circularity detected when computing ~a" fn-name)))))))
    (destructuring-bind (table . aux-tables) (ensure-list tables)
      (let* ((initial-alist (gethash node table)))
        (scan-alist initial-alist)
        (unless (or (eql fn-name 'attrs-invalid)
                    (let ((mask (attrs-invalid node)))
                      (or (eql mask t)
                          (member fn-name mask))))
          (dolist (table aux-tables)
            (scan-alist (gethash node table))))
        ;; Return the initial alist, which is all that should be
        ;; written to.
        (values initial-alist nil)))))

(defun cached-attr-fn (node fn-name)
  "Retrieve the cached value of FN-NAME on NODE, trying the ATTR-MISSING
function on it if not found at first."
  (declare (type function))
  (unless (boundp '*attrs*)
    (error (make-condition 'unbound-attrs :fn-name fn-name)))
  (let* ((tables (attrs-tables *attrs*)))
    (multiple-value-bind (alist p)
        (retrieve-memoized-attr-fn node fn-name tables)
      (when p (return-from cached-attr-fn (values-list (cdr p))))
      (attr-missing fn-name node)
      (setf (values alist p)
            (retrieve-memoized-attr-fn node fn-name tables))
      (if p
          (values-list (cdr p))
          ;; We tried once, it's still missing, so fail
          (block nil
            (when-let (proxy (attr-proxy node))
              (ignore-some-conditions (uncomputed-attr)
                (return (cached-attr-fn proxy fn-name))))
            ;; The proxy also failed.
            (error (make-condition 'uncomputed-attr :node node :fn fn-name)))))))

(defun memoize-attr-fun (node fn-name thunk)
  "Look for a memoized value for attr function FN-NAME on NODE.
If not there, invoke the thunk THUNK and memoize the values returned."
  (declare (type function thunk))
  (unless (boundp '*attrs*)
    (error (make-condition 'unbound-attrs :fn-name fn-name)))
  (let* ((tables (attrs-tables *attrs*))
         (table (car tables))
         (in-progress :in-progress))
    (multiple-value-bind (alist p)
        (retrieve-memoized-attr-fn node fn-name tables)
      (when p
        (typecase (cdr p)
          (list (return-from memoize-attr-fun (values-list (cdr p))))
          (t
           (assert (eql (cdr p) in-progress))
           (error "Circularity detected in ~a on ~a" fn-name node))))
      (let ((p (cons fn-name in-progress)))
        ;; additional pushes onto the alist may occur in the call to THUNK,
        ;; so get the push of p onto the list out of the way now.  If we
        ;; tried to assign after the call we might lose information.
        (unwind-protect
             (progn
               (setf (gethash node table) (cons p alist))
               (let ((vals (multiple-value-list (funcall thunk))))
                 (setf (cdr p) vals)
                 (values-list vals)))
          ;; If a non-local return occured from THUNK, we need
          ;; to remove p from the alist, otherwise we will never
          ;; be able to compute the function here
          (when (eql (cdr p) in-progress)
            (removef (gethash node table) p)))))))
  
(define-condition uncomputed-attr (error)
  ((node :initarg :node :reader uncomputed-attr-node)
   (fn :initarg :fn :reader uncomputed-attr-fn))
  (:report (lambda (condition stream)
             (format stream "Uncomputed attr function ~a on node ~a"
                     (uncomputed-attr-fn condition)
                     (uncomputed-attr-node condition)))))

(define-condition unbound-attrs (unbound-variable)
  ((fn-name :initarg :fn-name :initform nil
            :reader unbound-attrs-fn-name))
  (:documentation "Error to be used when *attrs* is unbound while calling an
 attrs function")
  (:report
   (lambda (condition stream)
     (with-slots (fn-name) condition
       (format stream
               "Special variable ~s unbound while trying to compute attribute ~s.
~s should be used to set ~s before trying to populate any attributes."
               '*attrs* fn-name 'with-attr-table '*attrs*)))))

(defgeneric attr-missing (fn-name node)
  (:documentation
   "Function invoked when an attr function has not been computed on NODE.
    The default method signals an error.")
  (:method ((fn-name symbol) (node node))
    (error (make-condition 'uncomputed-attr :node node :fn fn-name))))

(defun mapc-attrs (fn vals nodes)
  (mapc (lambda (node) (apply fn node vals)) nodes))

(defun mapc-attrs-children (fn vals node)
  (mapc-attrs fn vals (children node)))

(defun mapc-attrs-slot (fn vals node slot)
  (mapc-attrs fn vals (slot-value node slot)))

(def-attr-fun attrs-invalid (in)
  "Whether the attributes for an object are invalid.
Can return T to invalidate all attributes, or a list of attributes to
invalidate."
  (:method ((obj t) &optional in)
    in))

(defmethod attr-missing ((fn-name (eql 'attrs-invalid))
                         obj)
  (attrs-invalid obj nil))
