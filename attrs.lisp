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
  (:import-from :serapeum :defplace :assure :lret :defvar-unbound :with-thunk
                :defstruct-read-only :defsubst :standard/context :def)
  (:export
   :def-attr-fun
   :with-attr-table
   :with-attr-session
   :*attrs*
   :attrs-root*
   :attr-missing
   :attrs-root
   :attr-proxy
   :subroot
   :subroot?
   :attrs-root
   :unreachable-node
   :reachable?))

(in-package :functional-trees/attrs)
(in-readtable :curry-compose-reader-macros)


;;; Variables

(defvar-unbound *attrs*
  "Holds the current attribute session.")

;;; Use defparameter as we want the cache to be cleared if the system
;;; is reloaded.
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

(defvar *subroot-stack* nil
  "Stack of subroots whose attributes are being computed.
While subroots cannot be nested in the node tree, computation of their
attributes can be dynamically nested when one depends on the other.")

(defvar *cache-default* t
  "Whether to use the session cache by default.")

(defvar *inherit-default* t
  "Whether to inherit attr sessions by default.
Inheriting a session means that if there is already a session in
progress for root A, and you try to start a session for root B, then
if B is reachable from A the session for A is reused.")

(def +node->subroot/initial-size+ 4099
  "Initial size for the node->subroot table.
The value is heuristic, with the goal of minimizing the initial
rehashing for large tables.")


;;; Classes

(defclass attrs-root ()
  ((subroot-map
    :documentation "Tables from subroots to attributes and from subroots to dependencies."
    :type subroot-map
    :initarg :subroot-map))
  (:documentation "Mixin that marks a class as a root.
This is important; it controls subroot copying behavior."))

(defmethod copy :around ((root attrs-root) &key)
  "Carry forward (copying) the subroots from the old root."
  (let ((result (call-next-method)))
    (when-let (idx (subroot-map root))
      (setf (subroot-map result)
            (copy-subroot-map idx)))
    result))

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

(defstruct-read-only (subroot-map
                      (:conc-name subroot-map.)
                      (:constructor
                          make-subroot-map
                          (&key (subroot->attr-table (make-attr-table))
                             (subroot->deps (make-attr-table))
                             (ast->proxy (make-attr-table)))))
  "Data structure associated with a root to track its subroots."
  ;; Table from subroots to attributes
  (subroot->attr-table :type hash-table)
  ;; Table from subroots to dependencies
  (subroot->deps :type hash-table)
  ;; Table of AST proxies. These may be stored as attribute values so
  ;; they need to be copied along with the subroots.
  (ast->proxy :type hash-table))

(defmethod print-object ((self subroot-map) stream)
  (print-unreadable-object (self stream :type t :identity t)))

(defun copy-subroot-map (map)
  (make-subroot-map
   :subroot->attr-table
   (copy-attr-table (subroot-map.subroot->attr-table map))
   :subroot->deps (copy-attr-table (subroot-map.subroot->deps map))
   :ast->proxy (copy-attr-table (subroot-map.ast->proxy map))))

(defstruct-read-only (attrs
                      (:conc-name attrs.)
                      (:constructor make-attrs
                          (root &aux (node->subroot (compute-node->subroot root)))))
  "An attributes session.
This holds at least the root of the attribute computation."
  (root :type attrs-root)
  ;; Pre-computed table from nodes to their subroots.
  (node->subroot :type hash-table))

(defsubst attrs-root (attrs)
  (attrs.root attrs))

(defmethod fset:convert ((to (eql 'node)) (attrs attrs) &key)
  (attrs-root attrs))


;;; Subroot implementation

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

;;; A root node has an associated map of subroot nodes. When the root
;;; is copied, the new root gets its own copy of the map. The subroots
;;; are where the attributes are actually stored; each subroot has an
;;; attribute table.

;;; Subroots are invalidated as follows: of course, since functional
;;; trees are functional, when a given node is changed it and its
;;; parents (including its subroot) are replaced. Such replaced
;;; subroots that are no longer part of the tree are trivially
;;; invalid. Then, recursively, any subroot that depends on an invalid
;;; subroot is invalidated.

;;; Subroot dependencies are recorded when calculating the attributes.
;;; When an attribute is being calculated on a node, that node's
;;; dominating subroot is placed on a stack. All subroots already on
;;; the stack when calculating a node's attributes are marked as
;;; depending on the current nodes' dominating subroot.

(defun dominating-subroot (root node &key (error t))
  "Find the dominating subroot of NODE."
  (declare (optimize (debug 0)))        ;allow tail recursion
  ;; TODO Enforce that subroots cannot be nested?
  (let ((real-root (fset:convert 'node root))
        (real-node (fset:convert 'node node)))
    (cond ((eql real-root real-node) nil)
          ((subroot? real-node) real-node)
          (t
           (let ((rpath (rpath-to-node real-root real-node)))
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
                 (find-if #'subroot? rpath)))))))

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

(defun current-subroot (node)
  "Return the dominating subroot for NODE."
  (let ((attrs-root (attrs-root *attrs*)))
    (or (when (boundp '*attrs*)
          (let ((table (attrs.node->subroot *attrs*)))
            (or (gethash node table)
                (when-let (p (attr-proxy node))
                  (gethash p table)))))
        (dominating-subroot attrs-root node)
        attrs-root)))

(defun compute-node->subroot (ast)
  "Recurse over AST, computing a table from ASTs to their dominating subroots."
  (declare (optimize (debug 0)))
  (let ((table (make-hash-table :test 'eq :size +node->subroot/initial-size+)))
    (labels ((compute-node->subroot (ast &optional subroot)
               (let ((ast (fset:convert 'node ast)))
                 (cond ((null subroot)
                        (compute-node->subroot ast ast))
                       ((and (not (eq ast subroot))
                             (subroot? ast))
                        (compute-node->subroot ast ast))
                       (t
                        (setf (gethash ast table) subroot)
                        (dolist (c (children ast))
                          (compute-node->subroot c subroot)))))))
      (compute-node->subroot ast)
      table)))

(defun subroot-map (root &key (ensure t))
  "Get the subroot map for ROOT."
  (declare (attrs-root root))
  (assert (slot-exists-p root 'subroot-map))
  (if (slot-boundp root 'subroot-map)
      (slot-value root 'subroot-map)
      (and ensure
           (setf (slot-value root 'subroot-map)
                 (make-subroot-map)))))

(defun (setf subroot-map) (value root)
  "Set ROOT's subroot map to VALUE."
  (setf (slot-value root 'subroot-map)
        (assure subroot-map value)))

(defun attrs.subroot->attr-table (attrs &key (ensure t))
  "Get the subroots table for ATTRS.
If ENSURE is non-nil, create the table."
  (when-let (index
             (subroot-map (attrs-root attrs) :ensure ensure))
    (subroot-map.subroot->attr-table index)))

(defun attrs.subroot->deps (attrs &key (ensure t))
  "Get the subroot dependencies table for ATTRS.
If ENSURE is non-nil, create the table."
  (when-let (index
             (subroot-map (attrs-root attrs) :ensure ensure))
    (subroot-map.subroot->deps index)))

(defun attrs.ast->proxy (attrs &key (ensure t))
  "Get the attr proxy table for ATTRS.
If ENSURE is non-nil, create the table."
  (when-let (index
             (subroot-map (attrs-root attrs) :ensure ensure))
    (subroot-map.ast->proxy index)))

(defsubst attrs-root* ()
  "Get the root of the current attrs table."
  (attrs-root *attrs*))

(defun node-attr-table (node)
  (subroot-attr-table (current-subroot node)))

(defun subroot-attr-table (subroot &key ensure)
  "Get the attr table for SUBROOT in the current session."
  (when-let (subroots (attrs.subroot->attr-table *attrs* :ensure ensure))
    (ensure-gethash subroot
                    subroots
                    (make-attr-table))))

(defun subroot-deps (subroot)
  "Get the dependencies of SUBROOT in the current session."
  (gethash subroot (attrs.subroot->deps *attrs*)))

(defun (setf subroot-deps) (value subroot)
  (setf (gethash subroot (attrs.subroot->deps *attrs* :ensure t))
        (remove-if (compose #'null #'tg:weak-pointer-value)
                   value)))

(defplace attr-proxy (attr)
  (gethash attr (attrs.ast->proxy *attrs*)))

(defun call/attr-table (root fn &key
                                  (cache *cache-default*)
                                  (inherit *inherit-default*))
  "Invoke FN with an attrs instance for ROOT.
ROOT might be an attrs instance itself.

If the active attrs instance has ROOT for its root, it is not
replaced."
  (declare (optimize (debug 0)))
  (let* ((new nil)
         (*attrs*
           (cond
             ((typep root 'attrs) root)
             ((and cache (cache-lookup root)))
             ((and (boundp '*attrs*)
                   (or (eql (attrs-root *attrs*)
                            root)
                       (and inherit
                            (reachable? (attrs-root *attrs*) root))))
              *attrs*)
             (t
              (lret ((attrs (make-attrs root)))
                (when cache
                  (setf (cache-lookup root) attrs))
                (setf new t))))))
    (when new
      (invalidate-subroots *attrs*))
    (funcall fn)))

(defun invalidate-subroots (attrs)
  (let ((subroot->attr-table (attrs.subroot->attr-table attrs))
        (subroot->deps (attrs.subroot->deps attrs))
        (removed '()))
    (when (and subroot->attr-table subroot->deps)
      ;; Remove unreachable subroots from the table.
      (iter (for (subroot nil) in-hashtable subroot->attr-table)
            (unless
                ;; Cheap reachability check.
                (gethash subroot (attrs.node->subroot *attrs*))
              (remhash subroot subroot->attr-table)
              (remhash subroot subroot->deps)
              (push subroot removed)))
      ;; Uncache any suroot that depends on an unreachable subroot.
      (iter (for newly-removed-count =
                 (iter (for (subroot deps) in-hashtable subroot->deps)
                       (when (iter (for ptr in deps)
                                   (for dep = (tg:weak-pointer-value ptr))
                                   (thereis (not (gethash dep subroot->attr-table))))
                         (remhash subroot subroot->deps)
                         (remhash subroot subroot->attr-table)
                         (pushnew subroot removed)
                         (sum 1))))
            (until (zerop newly-removed-count))))
    removed))

(defun record-deps (root current-subroot subroot-stack)
  "Record CURRENT-SUBROOT as a dependency of the subroots in SUBROOT-STACK."
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
  (with-thunk (body)
    `(call/record-subroot-deps ,node ,body)))


;;; API

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
  (with-thunk (body)
    `(call/attr-table ,root ,body ,@args)))

(defmacro def-attr-fun (name (&rest optional-args) &body methods)
  (assert (symbolp name))
  (assert (every #'symbolp optional-args))
  (with-gensyms (node present?)
    (let ((docstring
            (when (stringp (car methods))
              (pop methods)))
          (body
            (let ((body '((call-next-method))))
              (with-thunk (body)
                `(memoize-attr-fun ,node ',name ,body)))))
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

(defun retrieve-memoized-attr-fn (node fn-name table)
  "Look up memoized value for FN-NAME on NODE.
Return the node's alist, and the pair for FN-NAME if the alist has
one."
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
  (declare (type function))
  (assert-attrs-bound fn-name)
  (let* ((table (node-attr-table node)))
    (multiple-value-bind (alist p)
        (retrieve-memoized-attr-fn node fn-name table)
      (when p (return-from cached-attr-fn (values-list (cdr p))))
      (attr-missing fn-name node)
      (setf (values alist p)
            (retrieve-memoized-attr-fn node fn-name table))
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
  (assert-attrs-bound fn-name)
  (let* ((table (node-attr-table node))
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

(defun assert-attrs-bound (fn-name)
  (unless (boundp '*attrs*)
    (error (make-condition 'unbound-attrs :fn-name fn-name))))

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

(defgeneric attr-missing (fn-name node)
  (:documentation
   "Function invoked when an attr function has not been computed on NODE.
    The default method signals an error.")
  (:method ((fn-name symbol) (node node))
    (error (make-condition 'uncomputed-attr :node node :fn fn-name))))
