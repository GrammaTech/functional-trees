(defpackage :functional-trees/attrs
  (:nicknames :ft/attrs)
  (:use
   :common-lisp :alexandria :iterate
   :functional-trees/functional-trees
   :curry-compose-reader-macros
   :named-readtables)
  (:shadowing-import-from :trivial-garbage :make-weak-hash-table)
  (:shadowing-import-from :fset :subst :subst-if :subst-if-not :mapcar :mapc)
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
   :attrs-root))

(in-package :functional-trees/attrs)
(in-readtable :curry-compose-reader-macros)

;;; Attributes are stored in a hash table mapping
;;; nodes to list of values.

(defstruct attrs
  (table (make-attr-table))
  (root  nil))

(declaim (special *attrs*))

(defun make-attr-table (&rest args)
  (multiple-value-call #'make-weak-hash-table
    :weakness :key
    :test #'eq
    (values-list args)))

(defun attrs-root* ()
  "Get the root of the current attrs table."
  (attrs-root *attrs*))

(defmacro with-attr-table (root &body body)
  "Create an ATTRS structure with root ROOT
   and bind it to *ATTRS*, then evaluate BODY
   in an implicit PROGN."
  `(let ((*attrs* (make-attrs :root ,root)))
     ,@body))

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
      `(defgeneric ,name (,node &optional ,@optional-args)
         ,@(when docstring `((:documentation ,docstring)))
         (:method :around (,node &optional ,@(when optional-args
                                               `((,(car optional-args) nil ,present?)
                                                 ,@(cdr optional-args))))
           ,@(when optional-args
               `((declare (ignorable ,@optional-args))))
           ,(if optional-args
                `(if ,present?
                     ,body
                     (cached-attr-fn ,node ',name))
                body))
         ,@methods))))

(defun retrieve-memoized-attr-fn (node fn-name table)
  "Look up memoized value for FN-NAME on NODE"
  (let* ((alist (gethash node table)))
    (iter (for p in alist)
          (when (eql (car p) fn-name)
            (etypecase (cdr p)
              (list (return-from retrieve-memoized-attr-fn (values alist p)))
              (t
               (assert (eql (cdr p) :in-progress))
               (error "Circularity detected when computing ~a" fn-name)))))
    (values alist nil)))

(defun cached-attr-fn (node fn-name)
  "Retrieve the cached value of FN-NAME on NODE, trying the ATTR-MISSING
function on it if not found at first."
  (declare (type function thunk))
  (let* ((table (attrs-table *attrs*)))
    (multiple-value-bind (alist p)
        (retrieve-memoized-attr-fn node fn-name table)
      (when p (return-from cached-attr-fn (values-list (cdr p))))
      (attr-missing fn-name node)
      (setf (values alist p)
            (retrieve-memoized-attr-fn node fn-name table))
      (unless p 
         ;; We tried once, it's still missing, so fail
        (error (make-condition 'uncomputed-attr :node node :fn fn-name)))
      (values-list (cdr p)))))

(defun memoize-attr-fun (node fn-name thunk)
  "Look for a memoized value for attr function FN-NAME on NODE.
If not there, invoke the thunk THUNK and memoize the values returned."
  (declare (type function thunk))
  (let* ((table (attrs-table *attrs*))
         (in-progress :in-progress))
    (multiple-value-bind (alist p)
        (retrieve-memoized-attr-fn node fn-name table)
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
