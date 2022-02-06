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
   :mapc-attrs
   :mapc-attrs-children
   :mapc-attrs-slot))

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

(defmacro with-attr-table (root &body body)
  "Create an ATTRS structure with root ROOT
   and bind it to *ATTRS*, then evaluate BODY
   in an implicit PROGN."
  `(let ((*attrs* (make-attrs :root ,root)))
     ,@body))

(defmacro def-attr-fun (name (&rest optional-args) &body methods)
  (assert (symbolp name))
  (assert (every #'symbolp optional-args))
           
  (with-gensyms (node fn)
    (let ((docstring
            (when (stringp (car methods))
              (pop methods))))
      `(defgeneric ,name (,node &optional ,@optional-args)
         ,@(when docstring `((:documentation ,docstring)))
         (:method :around (,node &optional ,@optional-args)
           (flet ((,fn () (call-next-method)))
             (declare (dynamic-extent #',fn))
             (memoize-attr-fun ,node ',name #',fn)))
         ,@methods))))

(defun memoize-attr-fun (node fn-name thunk)
  "Look for a memoized value for attr function FN-NAME on NODE.
If not there, invoke the thunk THUNK and memoize the values returned."
  (declaim (type function thunk))
  (let* ((table (attrs-table *attrs*))
         (alist (gethash node table)))
    (iter (for p in alist)
          (when (eql (car p) fn-name)
            (return-from memoize-attr-fun (values-list (cdr p)))))
    (let ((vals (multiple-value-list (funcall thunk))))
      (if alist
          (push (cons fn-name vals) (cdr alist))
          (setf (gethash node table)
                (list (cons fn-name vals))))
      (values-list vals))))
       
(defun mapc-attrs (fn vals nodes)
  (mapc (lambda (node) (apply fn node vals)) nodes))

(defun mapc-attrs-children (fn vals node)
  (mapc-attrs fn vals (children node)))

(defun mapc-attrs-slot (fn vals node slot)
  (mapc-attrs fn vals (slot-value node slot)))
