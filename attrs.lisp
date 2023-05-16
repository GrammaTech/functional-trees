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
  (:import-from :serapeum
                :standard/context :defplace :assure
                :filter-map :nlet :lret)
  (:export
   :def-attr-fun
   :with-attr-table
   :with-attr-session
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
   :unreachable-node))

(in-package :functional-trees/attrs)
(in-readtable :curry-compose-reader-macros)

;;; We want this to be cleared if the system is reloaded.
(defparameter *session-cache*
  (tg:make-weak-hash-table
   :test 'eq
   :weakness :key
   :weakness-matters t)
  "Global (weak) cache of attribute tables.
Roots are immutable, so if we have previously computed attributes for
them we can reuse them.")

(defplace cache-lookup (key)
  (gethash key *session-cache*))

(defclass attrs-root ()
  ((subroot-index
    :documentation "Tables from subroots to attributes and from subroots to dependencies."
    :initarg :subroot-index))
  (:documentation "Mixin that marks a class as a root.
This is important; it controls subroot copying behavior."))

;;; A root node has a set of subroot nodes. When the root is copied,
;;; the new root has the same list. The subroots are where the
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
  "Carry forward (copying) the subroots from the old root."
  (let ((result (call-next-method)))
    (when-let (idx (subroot-index root))
      (setf (subroot-index result)
            (copy-subroots-table idx)))
    result))

(defclass subroots-table ()
  ((subroot-node-attrs
    :initarg :subroot-node-attrs
    :type hash-table
    :reader subroots-table-subroots
    :documentation "Table from subroots to attributes")
   (subroot-deps
    :initarg :subroot-deps
    :type hash-table
    :reader subroots-table-subroot-deps
    :documentation "Table from subroots to dependencies")
   (proxies
    :documentation "Table of AST proxies.
These may be stored as attribute values so they need to be
copied along with the subroots."
    :initarg :proxies
    :type hash-table
    :reader subroots-table.proxies))
  (:default-initargs
   :subroot-node-attrs (make-attr-table)
   :subroot-deps (make-attr-table)
   :proxies (make-attr-table)))

(defun make-subroots-table (&rest args &key &allow-other-keys)
  (apply #'make-instance 'subroots-table args))

(defun copy-subroots-table (table)
  (with-slots (subroot-node-attrs subroot-deps proxies) table
    (make-subroots-table
     :subroot-node-attrs (copy-attr-table subroot-node-attrs)
     :subroot-deps (copy-attr-table subroot-deps)
     :proxies proxies)))

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

(defun dominating-subroot (root node &key (error t))
  "Find the dominating subroot of NODE."
  (declare (optimize (debug 0)))        ;allow tail recursion
  ;; TODO Enforce that subroots cannot be nested?
  (cond ((eql root node) nil)
        ((subroot? node) node)
        (t
         (let ((real-root (fset:convert 'node root))
               (real-node (fset:convert 'node node)))
           (unless (eql real-root real-node)
             (let ((rpath (ft::rpath-to-node real-root real-node)))
               (if (null rpath)
                   (if-let ((proxy (attr-proxy real-node)))
                     (dominating-subroot root proxy)
                     (progn
                       (when error
                         (cerror "Return nil"
                                 'unreachable-node
                                 :root root
                                 :node node))
                       nil))
                   (find-if #'subroot? rpath))))))))

(defun reachable? (root dest)
  "Is DEST reachable from ROOT?"
  (let* ((root-node (fset:convert 'node root))
         (dest-node (fset:convert 'node dest)))
    (or (eql root-node dest-node)
        (eql dest-node
             (nth-value 1
               (rpath-to-node root-node dest-node :error nil)))
        (when (boundp '*attrs*)
          (when-let ((proxy (attr-proxy dest-node)))
            (reachable? root proxy))))))

(defclass attrs ()
  ((root :initform (error "No root")
         :initarg :root
         :type attrs-root
         :reader attrs-root)
   (node-subroot-table
    :type hash-table
    :reader attrs-node-subroot-table
    :documentation "Pre-computed table from nodes to their subroots."
    :initarg :node-subroot-table))
  (:documentation "The table created by a `with-attr-table' form.
This holds at least the root of the attribute computation."))

(defmethod fset:convert ((to (eql 'node)) (attrs attrs) &key)
  (attrs-root attrs))

(defun make-attrs (&key root)
  "Make an instance of `attrs'."
  (make-instance 'attrs
    :root root
    :node-subroot-table
    (compute-node-subroot-table root)))

(declaim (special *attrs*))

(defun current-subroot (node)
  "Return the dominating subroot for NODE."
  (let ((attrs-root (attrs-root *attrs*)))
    (or (when (boundp '*attrs*)
          (let ((table (attrs-node-subroot-table *attrs*)))
            (or (gethash node table)
                (when-let (p (attr-proxy node))
                  (gethash p table)))))
        (dominating-subroot attrs-root node)
        attrs-root)))

(defvar *subroot-stack* nil
  "Stack of subroots whose attributes are being computed.
While subroots cannot be nested in the node tree, computation of their
attributes can be dynamically nested when one depends on the other.")

(defun compute-node-subroot-table (ast)
  "Recurse over AST, computing a table from ASTs to their dominating subroots."
  (declare (optimize (debug 0)))
  (let ((table (make-hash-table :test 'eq :size 4096)))
    (labels ((compute-node-subroot-table (ast &optional subroot)
               (let ((ast (if (typep ast 'node) ast
                              (fset:convert 'node ast))))
                 (cond ((null subroot)
                        (compute-node-subroot-table ast ast))
                       ((and (not (eq ast subroot))
                             (subroot? ast))
                        (compute-node-subroot-table ast ast))
                       (t
                        (setf (gethash ast table) subroot)
                        (dolist (c (children ast))
                          (compute-node-subroot-table c subroot)))))))
      (compute-node-subroot-table ast)
      table)))

(defun make-attr-table (&rest args)
  "Make a weak 'eq hash table."
  (multiple-value-call #'make-weak-hash-table
    :weakness :key
    :test #'eq
    (values-list args)))

(defun copy-attr-table (table-in &rest args)
  "Copy a weak 'eq hash table."
  (let ((table-out (apply #'make-attr-table :size (hash-table-size table-in) args)))
    (iter (for (k v) in-hashtable table-in)
          (setf (gethash k table-out) v))
    table-out))

(defun subroot-index (root &key (ensure t))
  "Get the subroot index for the current root."
  (declare (attrs-root root))
  (assert (slot-exists-p root 'subroot-index))
  (if (slot-boundp root 'subroot-index)
      (slot-value root 'subroot-index)
      (and ensure
           (setf (slot-value root 'subroot-index)
                 (make-subroots-table)))))

(defun attrs-subroots (attrs &key (ensure t))
  "Get the subroots table for ATTRS.
If ENSURE is non-nil, create the table."
  (when-let (index
             (subroot-index (attrs-root attrs) :ensure ensure))
    (subroots-table-subroots index)))

(defun attrs-subroot-deps (attrs &key (ensure t))
  "Get the subroot dependencies table for ATTRS.
If ENSURE is non-nil, create the table."
  (when-let (index
             (subroot-index (attrs-root attrs) :ensure ensure))
    (subroots-table-subroot-deps index)))

(defun attrs-proxies (attrs &key (ensure t))
  "Get the attr proxy table for ATTRS.
If ENSURE is non-nil, create the table."
  (when-let (index
             (subroot-index (attrs-root attrs) :ensure ensure))
    (subroots-table.proxies index)))

(defun attrs-root* ()
  "Get the root of the current attrs table."
  (attrs-root *attrs*))

(defun node-subroot-table (node)
  "Get the subroot table for the dominating subroot of NODE."
  (subroot-table (current-subroot node)))

(defun subroot-table (subroot &key ensure)
  "Get the subroot table for SUBROOT in the current attrs."
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

(defun set-attr-proxy (attr value)
  (setf (gethash attr (attrs-proxies *attrs*))
        value))

(defun (setf attr-proxy) (value attr)
  (set-attr-proxy attr value))

(defun call/attr-table (root fn &key
                                  cache
                                  inherit)
  "Invoke FN with an attrs instance for ROOT.
ROOT might be an attrs instance itself.

If the active attrs instance has ROOT for its root, it is not
replaced."
  (declare (optimize (debug 0)))
  (let* ((new nil)
         (*attrs*
           (cond
             ((typep root 'attrs) root)
             ((and (boundp '*attrs*)
                   (if inherit
                       (progn
                         (assert (reachable? (attrs-root *attrs*) root))
                         t)
                       (eql (attrs-root *attrs*)
                            root)))
              *attrs*)
             (t
              (or (and cache
                       (cache-lookup root))
                  (serapeum:lret ((attrs (make-attrs :root root)))
                    (when cache
                      (setf (cache-lookup root) attrs))
                    (setf new t)))))))
    (when new
      (invalidate-subroots *attrs*))
    (funcall fn)))

(defun invalidate-subroots (attrs)
  (let ((subroots-table (attrs-subroots attrs))
        (subroot-deps (attrs-subroot-deps attrs))
        (removed '()))
    (when (and subroots-table subroot-deps)
      ;; Remove unreachable subroots from the table.
      (iter (for (subroot nil) in-hashtable subroots-table)
            (unless (gethash subroot (attrs-node-subroot-table *attrs*))
              (remhash subroot subroots-table)
              (remhash subroot subroot-deps)
              (push subroot removed)))
      ;; Uncache any suroot that depends on an unreachable subroot.
      (iter (for newly-removed-count =
                 (iter (for (subroot deps) in-hashtable subroot-deps)
                       (when (iter (for ptr in deps)
                                   (for dep = (tg:weak-pointer-value ptr))
                                   (thereis (not (gethash dep subroots-table))))
                         (remhash subroot subroot-deps)
                         (remhash subroot subroots-table)
                         (pushnew subroot removed)
                         (sum 1))))
            (until (zerop newly-removed-count))))
    removed))

(defmacro with-attr-table (root &body body)
  "Create an ATTRS structure with root ROOT
   and bind it to *ATTRS*, then evaluate BODY
   in an implicit PROGN.  If ROOT is an ATTRS
   structure, simply bind *ATTRS* to it."
  `(with-attr-session (,root)
     ,@body))

(defmacro with-attr-session ((root &rest args &key &allow-other-keys)
                             &body body)
  "Like `with-attr-table', but allowing keyword arguments."
  (with-gensyms (attr-table-fn)
    `(flet ((,attr-table-fn () ,@body))
       (declare (dynamic-extent #',attr-table-fn))
       (call/attr-table ,root #',attr-table-fn ,@args))))

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

(defun record-deps (root current-subroot subroot-stack)
  (unless (eql root current-subroot)
    (iter (for depender in subroot-stack)
          ;; Avoid circular dependencies.
          (unless (eql current-subroot depender)
            (unless (member current-subroot
                            (subroot-deps depender)
                            :key #'tg:weak-pointer-value)
              (push (tg:make-weak-pointer current-subroot)
                    (subroot-deps depender)))))))

(defun call/record-subroot-deps (node fn &aux (root (attrs-root*)))
  (if (eql node root)
      ;; If we are computing top-down (after an attr-missing call),
      ;; mask the subroot stack.
      (let ((*subroot-stack* '()))
        (funcall fn))
      (let* ((current-subroot (current-subroot node))
             (*subroot-stack*
               (if (subroot? current-subroot)
                   (adjoin current-subroot *subroot-stack*)
                   ;; The "current subroot" is really the root.
                   *subroot-stack*)))
        (record-deps root current-subroot (rest *subroot-stack*))
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
