(defpackage :functional-trees/attrs
  (:nicknames :ft/attrs)
  (:use
   :common-lisp :alexandria :iterate
   :functional-trees/functional-trees
   :curry-compose-reader-macros
   :named-readtables)
  (:import-from :fset)
  (:shadowing-import-from :trivial-garbage :make-weak-hash-table)
  (:shadowing-import-from :fset :subst :subst-if :subst-if-not :mapcar :mapc)
  (:import-from :serapeum :standard/context :defplace :assure :filter-map)
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
   :has-attributes-p
   :has-attribute-p
   :subroot
   :subroot?
   :attrs-root
   :attrs-node
   :subroot-path
   :subroot-lookup
   :unreachable-node))

(in-package :functional-trees/attrs)
(in-readtable :curry-compose-reader-macros)

;;; Attributes are stored in a hash table mapping
;;; nodes to list of values.

(defclass attrs-root ()
  (;; Would this be better? An extra slot per AST vs. an extra hash
   ;; table lookup per AST*copies.
   (subroot-index :initarg :subroot-index))
  (:documentation "Mixin that marks a class as a root.
This is important; it controls subroot copying behavior."))

;;; A root node has a "list" of subroot nodes. When the root is
;;; copied, the new root has the same list. The subroots are where the
;;; attributes are actually stored; each subroot has an attribute
;;; table.

;;; Subroots are invalidated as follows: of course, since functional
;;; trees are functional, when a given node is changed it and its
;;; parents (including its subroot) are replaced. Subroots that are no
;;; longer part of the tree are trivially invalid. Then, recursively,
;;; any subroot that depends on an invalid subroot is invalidated.

;;; Subroot dependencies are recorded when calculating the attributes.
;;; When an attribute is being calculated on a node, that node's
;;; dominating subroot is placed on a stack. All subroots already on
;;; the stack when calculating a node's attributes are marked as
;;; depending on the current nodes' dominating subroot.

(defmethod copy :around ((root attrs-root) &key)
  (let ((result (call-next-method)))
    (when-let (idx (subroot-index root))
      (setf (subroot-index result)
            (copy-subroot-index-entry idx)))
    result))

(defstruct (subroot-index-entry (:copier nil))
  (subroots (make-attr-table) :read-only t :type hash-table)
  (subroot-deps (make-attr-table) :read-only t :type hash-table))

(defun copy-subroot-index-entry (entry)
  (make-subroot-index-entry
   :subroots (copy-attr-table (subroot-index-entry-subroots entry))
   :subroot-deps (copy-attr-table (subroot-index-entry-subroot-deps entry))))

(defclass subroot ()
  ()
  (:documentation "Mixin that marks a class as a subroot.
This is for convenience and entirely equivalent to specializing
`subroot?' to return non-nil."))

(defgeneric subroot? (x)
  (:documentation "Is X a subroot?")
  (:method ((x t))
    nil)
  (:method ((x subroot))
    t))

(defgeneric subroot-path (root subroot)
  (:documentation "Return the path from ROOT to SUBROOT.")
  (:method ((root node) (subroot node))
    (path-of-node root subroot))
  (:method (root subroot)
    (subroot-path (fset:convert 'node root)
                  (fset:convert 'node subroot))))

(defgeneric subroot-lookup (root path)
  (:documentation "Lookup PATH in ROOT.")
  (:method ((root node) (path list))
    (fset:lookup root path))
  (:method ((root node) (path node))
    (fset:lookup root path))
  (:method (root (path list))
    (subroot-lookup (fset:convert 'node root)
                    path))
  (:method (root path)
    (subroot-lookup (fset:convert 'node root)
                    (fset:convert 'node path))))

(defun dominating-subroot (root node &key (error t))
  "Dominating subroot of NODE."
  ;; TODO Enforce that subroots cannot be nested?
  (cond ((eql root node) nil)
        ((subroot? node) node)
        (t
         (let ((path (subroot-path root node))
               (real-node (fset:convert 'node node)))
           (if (null path)
               (if (eql (fset:convert 'node root)
                        real-node)
                   nil
                   (if-let ((proxy (attr-proxy real-node)))
                     (dominating-subroot root proxy)
                     (progn
                       (when error
                         (cerror "Continue" 'unreachable-node
                                 :root root
                                 :node node))
                       nil)))
               (iter (for subpath on (rest (reverse path)))
                     (for parent = (subroot-lookup root (reverse subpath)))
                     (finding parent such-that (subroot? parent))))))))

(defun reachable? (root node)
  (let* ((real-root (fset:convert 'node root))
         (real-node (fset:convert 'node node)))
    (or (eql real-root real-node)
        (when-let ((path (path-of-node real-root real-node :error nil)))
          (eql real-node (fset:lookup real-root path)))
        (when (boundp '*attrs*)
          (when-let ((proxy (attr-proxy real-node)))
            (reachable? root proxy))))))

(defclass attrs ()
  ((proxies :initform (make-attr-table) :reader attrs-proxies :type hash-table)
   (root :initform (error "No root")
         :initarg :root
         :type attrs-root
         :reader attrs-root)))

(defun make-attrs (&key root)
  (make-instance 'attrs :root root))

(declaim (special *attrs*))

(defun current-subroot (node)
  (let ((attrs-root (attrs-root *attrs*)))
    (or (dominating-subroot attrs-root node)
        attrs-root)))

(defvar *subroot-stack* nil
  "Stack of subroots whose attributes are being computed.
While subroots cannot be nested in the node tree, computation of their
attributes can be dynamically nested when one depends on the other.")
(declaim (special *subroot-stack*))

(defun make-attr-table (&rest args)
  (multiple-value-call #'make-weak-hash-table
    :weakness :key
    :test #'eq
    (values-list args)))

(defun copy-attr-table (table-in &rest args)
  (let ((table-out (apply #'make-attr-table :size (hash-table-size table-in) args)))
    (iter (for (k v) in-hashtable table-in)
          (setf (gethash k table-out) v))
    table-out))

(defvar *subroot-registry* (make-attr-table))

(defun subroot-index (root &key (ensure t))
  (declare (attrs-root root))
  (if (slot-boundp root 'subroot-index)
      (slot-value root 'subroot-index)
      (and ensure
           (setf (slot-value root 'subroot-index)
                 (make-subroot-index-entry)))))

(defun (setf subroot-index) (value root)
  (setf (slot-value root 'subroot-index) value))

(defun attrs-subroots (attrs &key (ensure t))
  (when-let (index
             (subroot-index (attrs-root attrs) :ensure ensure))
    (subroot-index-entry-subroots index)))

(defun attrs-subroot-deps (attrs &key (ensure t))
  (when-let (index
             (subroot-index (attrs-root attrs) :ensure ensure))
    (subroot-index-entry-subroot-deps index)))

(defun attrs-root* ()
  "Get the root of the current attrs table."
  (attrs-root *attrs*))

(defun node-subroot-table (node)
  (subroot-table (current-subroot node)))

(defun subroot-table (subroot &key ensure)
  (when-let (subroots (attrs-subroots *attrs* :ensure ensure))
    (ensure-gethash subroot
                    subroots
                    (make-attr-table))))

(defun subroot-deps (subroot)
  (gethash subroot (attrs-subroot-deps *attrs*)))

(defun (setf subroot-deps) (value subroot)
  (setf (gethash subroot (attrs-subroot-deps *attrs* :ensure t))
        (remove-if (compose #'null #'tg:weak-pointer-value)
                   value)))

(defun subroot-tables (node)
  (let ((subroot (current-subroot node)))
    (assure (cons hash-table t)
      (cons (subroot-table subroot :ensure t)
            (mapcar (compose #'subroot-table #'tg:weak-pointer-value)
                    (subroot-deps subroot))))))

(defun attr-proxy (attr)
  (gethash attr (attrs-proxies *attrs*)))

(defun (setf attr-proxy) (value attr)
  (setf (gethash attr (attrs-proxies *attrs*))
        value))

(defun call/attr-table (root fn)
  "Invoke FN with an attrs instance for ROOT.
ROOT might be an attrs instance itself.

If the active attrs instance has ROOT for its root, it is not
replaced."
  (declare (optimize (debug 0)))
  (let ((*attrs*
          (cond
            ((typep root 'attrs) root)
            ((and (boundp '*attrs*)
                  (eql (attrs-root *attrs*)
                       root))
             *attrs*)
            (t (make-attrs :root root)))))
    (invalidate-subroots *attrs*)
    (funcall fn)))

(defun invalidate-subroots (attrs)
  (let ((root (attrs-root attrs))
        (subroots-table (attrs-subroots attrs))
        (subroot-deps (attrs-subroot-deps attrs))
        (removed '()))
    (when (and subroots-table subroot-deps)
      ;; Remove unreachable subroots from the table.
      (iter (for (subroot nil) in-hashtable subroots-table)
            (unless (reachable? root subroot)
              (remhash subroot subroots-table)
              (remhash subroot subroot-deps)
              (push subroot removed)))
      ;; Uncache any suroot that depends on an unreachable subroot.
      (iter (for newly-removed =
                 (iter (for (subroot deps) in-hashtable subroot-deps)
                       (when (iter (for ptr in deps)
                                   (for dep = (tg:weak-pointer-value ptr))
                                   (thereis (not (gethash dep subroots-table))))
                         (remhash subroot subroot-deps)
                         (remhash subroot subroots-table)
                         (pushnew subroot removed)
                         (collect subroot))))
            (while newly-removed)))
    removed))

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
           (with-record-subroot-deps (,node)
             ,(if optional-args
                  `(if ,present?
                       ,body
                       (cached-attr-fn ,node ',name))
                  body)))
         ,@methods))))

(defun has-attributes-p (node &aux (tables (subroot-tables node)))
  (loop for table in tables
        thereis (nth-value 1 (gethash node table))))

(defun has-attribute-p (node fn-name &aux (tables (subroot-tables node)))
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
                      (error "Circularity detected when computing ~a on ~a" fn-name node)))))))
    (destructuring-bind (table . aux-tables) (ensure-list tables)
      (let* ((initial-alist (gethash node table)))
        (scan-alist initial-alist)
        (dolist (table aux-tables)
          (scan-alist (gethash node table)))
        ;; Return the initial alist, which is all that should be
        ;; written to.
        (values initial-alist nil)))))

(defun cached-attr-fn (node fn-name)
  "Retrieve the cached value of FN-NAME on NODE, trying the ATTR-MISSING
function on it if not found at first."
  (declare (type function))
  (unless (boundp '*attrs*)
    (error (make-condition 'unbound-attrs :fn-name fn-name)))
  (let* ((tables (subroot-tables node)))
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
  (let* ((tables (subroot-tables node))
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
               (let ((vals (multiple-value-list
                            (funcall thunk))))
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

(define-condition unreachable-node (error)
  ((root :initarg :root)
   (node :initarg :node))
  (:report
   (lambda (c s)
     (with-slots (root node) c
       (format s "~a is not reachable from ~a" node root)))))

(defun call/record-subroot-deps (node fn &aux (root (attrs-root*)))
  (declare (optimize (debug 0)))        ;Tail call
  (if (eql node root)
      ;; If we are computing top-down (after an attr-missing call),
      ;; mask the subroot stack.
      (let ((*subroot-stack* '()))
        (funcall fn))
      (let* ((current-subroot (current-subroot node))
             (*subroot-stack*
               (remove-if-not #'subroot?
                              (cons current-subroot *subroot-stack*))))
        (iter (for depender in (rest *subroot-stack*))
              ;; Avoid circular dependencies.
              (unless (or (eql current-subroot depender)
                          (or (eql current-subroot root)))
                (unless (member current-subroot
                                (subroot-deps depender)
                                :key #'tg:weak-pointer-value)
                  (push (tg:make-weak-pointer current-subroot)
                        (subroot-deps depender)))))
        (funcall fn))))

(defmacro with-record-subroot-deps ((node) &body body)
  (with-gensyms (fn)
    `(flet ((,fn () ,@body))
       (declare (dynamic-extent #',fn))
       (call/record-subroot-deps ,node #',fn))))

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
