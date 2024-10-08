(defpackage :functional-trees/attrs
  (:nicknames :ft/attrs)
  (:use
   :common-lisp :alexandria :iterate
   :functional-trees/functional-trees
   :curry-compose-reader-macros
   :named-readtables)
  (:import-from :fset)
  (:import-from :cl-store)
  (:import-from :closer-mop)
  (:shadowing-import-from :trivial-garbage :make-weak-hash-table)
  (:shadowing-import-from :fset :subst :subst-if :subst-if-not :mapcar :mapc)
  (:import-from :serapeum :defplace :assure :lret :defvar-unbound :with-thunk
                :defstruct-read-only :defsubst :standard/context :def
                :slot-value-safe :with-boolean :boolean-unless
                :nlet :and-let*)
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
   :reachable?
   :session-shadowing
   :recompute-subroot-mapping
   :attribute-error
   :circular-attribute
   :uncomputed-attr
   :has-attribute-p))

(in-package :functional-trees/attrs)
(in-readtable :curry-compose-reader-macros)


;;; Variables

(defvar-unbound *attrs*
  "Holds the current attribute session.")

(defvar *enable-cross-session-cache* t
  "If non-nil, cache attributes across sessions.")

;;; Use defparameter as we want the cache to be cleared if the system
;;; is reloaded.
(defparameter *session-cache*
  (tg:make-weak-hash-table
   :test 'eq
   :weakness :key
   :weakness-matters t)
  "Global (weak) cache of attribute sessions.
Roots are immutable, so if we have previously computed attributes for
them we can reuse them.

Practically this has the effect that we do not have to to recompute
the node->subroot table.")

(defplace cache-lookup (key)
  (gethash key *session-cache*))

(defvar *subroot-stack* nil
  "Stack of subroots whose attributes are being computed.
While subroots cannot be nested in the node tree, computation of their
attributes can be dynamically nested when one depends on the other.")

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
    :type (or subroot-map subroot-map-pointer)
    :initarg :subroot-map))
  (:documentation "Mixin that marks a class as a root.
This is important; it controls subroot copying behavior."))

(defmethod cl-store:serializable-slots :around ((self attrs-root))
  (remove 'subroot-map
          (call-next-method)
          :key #'closer-mop:slot-definition-name))

(defmethod copy :around ((root attrs-root) &key)
  "Carry forward (copying) the subroots from the old root."
  (lret ((result (call-next-method)))
    (if *enable-cross-session-cache*
        (when-let (old-map (slot-value-safe root 'subroot-map))
          (setf (slot-value result 'subroot-map)
                (fset:convert 'subroot-map-pointer old-map)))
        (slot-makunbound result 'subroot-map))))

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

(defstruct-read-only (subroot-map-pointer
                      (:conc-name subroot-map-pointer.)
                      (:constructor make-subroot-map-pointer (map)))
  "A pointer to a subroot map.
This allows the subroot-map to be copy-on-access, so a chain of updates
that don't access the subroot-map don't copy a lot of hash tables."
  (map :type subroot-map))

(defmethod fset:convert ((to (eql 'subroot-map)) (x subroot-map) &key)
  x)

(defmethod fset:convert ((to (eql 'subroot-map)) (x subroot-map-pointer) &key)
  (copy-subroot-map (subroot-map-pointer.map x)))

(defmethod fset:convert ((to (eql 'subroot-map-pointer)) (x subroot-map) &key)
  (make-subroot-map-pointer x))

(defmethod fset:convert ((to (eql 'subroot-map-pointer)) (x subroot-map-pointer) &key)
  x)

(defmethod print-object ((self subroot-map) stream)
  (print-unreadable-object (self stream :type t :identity t)))

(defun copy-subroot-map (map)
  (make-subroot-map
   :subroot->attr-table
   (copy-attr-table (subroot-map.subroot->attr-table map))
   :subroot->deps (copy-attr-table (subroot-map.subroot->deps map))
   :ast->proxy (copy-attr-table (subroot-map.ast->proxy map))))

(def +empty-hash-table+
  (load-time-value (make-hash-table) t))

(defstruct-read-only (attrs
                      (:conc-name attrs.)
                      (:constructor make-attrs
                          (root &aux (node->subroot
                                      (if *enable-cross-session-cache*
                                          (compute-node->subroot root)
                                          +empty-hash-table+)))))
  "An attribute session.
This holds at least the root of the attribute computation."
  (root :type attrs-root)
  ;; This is only used if *enable-cross-session-cache* is nil.
  (table
   (if *enable-cross-session-cache*
       +empty-hash-table+
       (make-attr-table))
   :type hash-table)
  ;; Pre-computed table from nodes to their subroots.
  (node->subroot :type hash-table))

(defsubst has-attr-table? (attrs)
  (not (eql +empty-hash-table+ (attrs.table attrs))))

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
  (nlet retry ()
    (let ((attrs-root (attrs-root *attrs*)))
      (restart-case
          (or (when (boundp '*attrs*)
                (let ((table (attrs.node->subroot *attrs*)))
                  (or (gethash node table)
                      (when-let (p (attr-proxy node))
                        (gethash p table)))))
              (dominating-subroot attrs-root node)
              attrs-root)
        (recompute-subroot-mapping ()
          :report "Recompute node-subroot mapping in tree"
          (recompute-subroot-mapping)
          (retry))))))

(defun make-node->subroot-table ()
  (tg:make-weak-hash-table
   :test 'eq
   :weakness :key
   :size +node->subroot/initial-size+))

(defun compute-node->subroot (ast &key (table (make-node->subroot-table)) force)
  "Recurse over AST, computing a table from ASTs to their dominating subroots."
  (declare (optimize (debug 0)))
  (let ((first-time
          (or force
              (= 0 (hash-table-count table)))))
    ;; Using `with-boolean' means we only actually dispatch once on
    ;; `first-time' outside the loop, so we aren't paying for lookups
    ;; on the first computation.
    (with-boolean (first-time)
      (labels ((compute-node->subroot (ast subroot)
                 (let ((ast
                         (if (typep ast 'node) ast
                             (fset:convert 'node ast))))
                   (if (null subroot)
                       (compute-node->subroot ast ast)
                       (progn
                         (boolean-unless first-time
                           ;; If the subroot hasn't changed, the
                           ;; subroots of the children can't have
                           ;; changed and we don't need to walk them
                           ;; again.
                           (let ((old (gethash ast table)))
                             (when (eql old subroot)
                               (return-from compute-node->subroot))))
                         (cond ((and (not (eq ast subroot))
                                     (subroot? ast))
                                (compute-node->subroot ast ast))
                               (t
                                (setf (gethash ast table) subroot)
                                (dolist (c (children ast))
                                  (compute-node->subroot c subroot)))))))))
        (compute-node->subroot ast nil)
        table))))

(defun recompute-subroot-mapping (&optional (attrs *attrs*))
  "Recompute the node-to-subroot mapping of ATTRS.
This should be done if the root has been mutated."
  (declare (attrs attrs))
  (compute-node->subroot
   (attrs.root attrs)
   :table (attrs.node->subroot attrs))
  attrs)

(defun subroot-map (root &key (ensure t))
  "Get the subroot map for ROOT."
  (declare (attrs-root root))
  (assert (slot-exists-p root 'subroot-map))
  (if (slot-boundp root 'subroot-map)
      (let ((value (slot-value root 'subroot-map)))
        (if (typep value 'subroot-map) value
            (setf (slot-value root 'subroot-map)
                  (fset:convert 'subroot-map value))))
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
  (if *enable-cross-session-cache*
      (subroot-attr-table (current-subroot node))
      (attrs.table *attrs*)))

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

(defun call/attr-session (root fn &key
                                    (inherit *inherit-default*)
                                    (shadow t)
                                    (cache *enable-cross-session-cache*))
  "Invoke FN with an attrs instance for ROOT.
ROOT might be an attrs instance itself.

If the active attrs instance has ROOT for its root, it is not
replaced.

If CACHE is non-nil, attributes may be cached across sessions.

If INHERIT is non-nil, the dynamically enclosing attr session may be
reused if ROOT is reachable from the outer session's root.

If SHADOW is T, then the new attribute session may shadow an enclosing
attribute session. The behavior is different depending on INHERIT.

SHADOW T -> No error
SHADOW nil, INHERIT nil -> Error on shadowing
SHADOW nil, INHERIT T -> Error on shadowing, unless inherited"
  (declare (optimize (debug 0)))
  (let* ((new nil)
         (*enable-cross-session-cache* cache)
         (*attrs*
           (cond
             ((typep root 'attrs) root)
             ((and cache (cache-lookup root)))
             ((and (boundp '*attrs*)
                   inherit
                   (reachable? (attrs-root *attrs*) root))
              *attrs*)
             ((and (boundp '*attrs*)
                   (not shadow))
              (error 'session-shadowing
                     :outer (attrs-root *attrs*)
                     :inner root
                     :inherit inherit))
             (t
              (lret ((attrs (make-attrs root)))
                (when cache
                  (setf (cache-lookup root) attrs))
                (setf new t))))))
    (unless (eql cache (not (has-attr-table? *attrs*)))
      (error "Cannot inherit with differing values for caching"))
    (when (and cache new)
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
  (cond ((not *enable-cross-session-cache*)
         (funcall fn))
        ((eql node root)
         ;; If we are computing top-down (after an attr-missing call),
         ;; mask the subroot stack.
         (let ((*subroot-stack* '()))
           (funcall fn)))
        (t
         (let* ((current-subroot (current-subroot node))
                (*subroot-stack*
                  (if (subroot? current-subroot)
                      (adjoin current-subroot *subroot-stack*)
                      ;; If there is no subroot but there is a subroot
                      ;; stack, that also means we're computing
                      ;; top-down and should mask the subroot stack.
                      '())))
           (record-deps root current-subroot *subroot-stack*)
           (funcall fn)))))

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
    `(call/attr-session ,root ,body ,@args)))

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
               (error 'circular-attribute :fn fn-name :node node)))))
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
           (error 'circular-attribute :node node :fn fn-name))))
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

(define-condition attribute-error (error)
  ((node :initarg :node :reader attribute-error-node)
   (fn :initarg :fn :reader attribute-error-function)))

(define-condition circular-attribute (attribute-error)
  ((node :reader circular-attribute-node)
   (fn :reader circular-attribute-function))
  (:report (lambda (c s)
             (with-slots (node fn) c
               (format s "Circularity detected in ~a on ~a" fn node)))))

(define-condition uncomputed-attr (attribute-error)
  ((node :reader uncomputed-attr-node)
   (fn :reader uncomputed-attr-function))
  (:report (lambda (condition stream)
             (format stream "Uncomputed attr function ~a on node ~a"
                     (uncomputed-attr-function condition)
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

(define-condition session-shadowing (error)
  ((outer :initarg :outer)
   (inner :initarg :inner)
   (inherit :initarg :inherit))
  (:report
   (lambda (c s)
     (with-slots (outer inner inherit) c
       (format s "Attempt to shadow attribute session for ~a by~@[ unrelated~] session for ~a"
               outer
               inherit
               inner)))))

(defgeneric attr-missing (fn-name node)
  (:documentation
   "Function invoked when an attr function has not been computed on NODE.
    The default method signals an error.")
  (:method ((fn-name symbol) (node node))
    (error (make-condition 'uncomputed-attr :node node :fn fn-name))))

(defun has-attribute-p (node &optional (attr-name nil attr-name-supplied-p))
  "Does NODE have attribute ATTR-NAME computed?
If ATTR-NAME is not supplied, return T if NODE has any attributes."
  (declare (symbol attr-name))
  (when (boundp '*attrs*)
    (and-let* ((table (node-attr-table node))
               (alist (gethash node table)))
      (if attr-name-supplied-p
          (assoc attr-name alist)
          alist))))
