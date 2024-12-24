(defpackage :functional-trees/attrs
  (:nicknames :ft/attrs)
  (:use
   :common-lisp
   :alexandria
   :curry-compose-reader-macros
   :functional-trees/functional-trees
   :iterate
   :named-readtables)
  (:import-from :cl-store)
  (:import-from :closer-mop)
  (:import-from :fset)
  (:shadowing-import-from
    :trivial-garbage
    :make-weak-hash-table)
  (:shadowing-import-from
    :fset
    :mapc
    :mapcar
    :subst
    :subst-if
    :subst-if-not)
  (:import-from
    :serapeum
    :@
    :and-let*
    :assure
    :boolean-unless
    :bound-value
    :box
    :boxp
    :def
    :defplace
    :defstruct-read-only
    :defsubst
    :defvar-unbound
    :lret
    :nlet
    :slot-value-safe
    :unbox
    :standard/context
    :with-boolean
    :with-thunk)
  (:export
   :*attrs*
   :*enable-cross-session-cache*
   :attr-missing
   :attr-proxy
   :attribute-error
   :attrs-root
   :attrs-root
   :attrs-root*
   :circular-attribute
   :def-attr-fun
   :has-attribute-p
   :reachable?
   :update-subroot-mapping
   :session-shadowing
   :subroot
   :subroot?
   :uncomputed-attr
   :unreachable-node
   :with-attr-session
   :with-attr-table))

(in-package :functional-trees/attrs)
(in-readtable :curry-compose-reader-macros)


;;; Variables

(defvar-unbound *attrs*
  "Holds the current attribute session.")

(defvar *attribute-trail* nil
  "Holds a stack-allocated list of (fn-name . node) pairs currently
being calculated, useful when diagnosing circular dependencies between
attributes.")

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

Practically this has the effect that we do not have to to update
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
    :type (or subroot-map box)
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
                (if (boxp old-map) old-map (box old-map))))
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
                             (node->proxy (make-attr-table)))))
  "Data structure associated with a root to track its subroots."
  ;; Table from subroots to attributes
  (subroot->attr-table :type hash-table)
  ;; Table from subroots to dependencies
  (subroot->deps :type hash-table)
  ;; Table of node proxies. These may be stored as attribute values so
  ;; they need to be copied along with the subroots.
  (node->proxy :type hash-table))

(defmethod print-object ((self subroot-map) stream)
  (print-unreadable-object (self stream :type t :identity t)))

(defun copy-subroot->attr-table (table)
  "Copy the subroot->attr table, ensuring each attr table is a fresh
table with fresh alists for its values."
  ;; TODO Use a different data structure.
  (lret ((table (copy-attr-table table)))
    (iter (for (subroot attr-table) in-hashtable table)
          (let ((attr-table (copy-attr-table attr-table)))
            (setf (@ table subroot) attr-table)
            (iter (for (node attrs) in-hashtable attr-table)
                  (setf (@ attr-table node)
                        (mapcar #'copy-list attrs)))))))

(defun copy-subroot-map (map)
  (make-subroot-map
   :subroot->attr-table
   (copy-subroot->attr-table (subroot-map.subroot->attr-table map))
   :subroot->deps (copy-attr-table (subroot-map.subroot->deps map))
   :node->proxy (copy-attr-table (subroot-map.node->proxy map))))

(def +empty-hash-table+
  #.(make-hash-table :size 0))

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

(defun reachable-in-cache? (node &key (proxy t))
  (when-let (attrs (bound-value '*attrs*))
    (let ((node->subroot (attrs.node->subroot attrs))
          (node (fset:convert 'node node)))
      (or (@ node->subroot node)
          (when-let (proxy (and proxy (attr-proxy node)))
            (@ node->subroot proxy))))))

(defun reachable-from-root? (root dest &key (proxy t))
  "Is DEST reachable from ROOT?"
  (let* ((root-node (fset:convert 'node root))
         (dest-node (fset:convert 'node dest)))
    (or (eql root-node dest-node)
        (eql dest-node
             (nth-value 1
               (rpath-to-node root-node dest-node :error nil)))
        (when (and proxy (boundp '*attrs*))
          (when-let ((proxy (attr-proxy dest-node)))
            (reachable-from-root? root proxy))))))

(defun reachable? (dest &key
                          (proxy t)
                          use-cache
                          (from (attrs-root*)))
  (if use-cache
      (or (reachable-in-cache? dest :proxy proxy)
          (reachable-from-root? from dest :proxy proxy))
      (reachable-from-root? from dest :proxy proxy)))

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
        (update-subroot-mapping ()
          :report "Update node-subroot mapping in tree"
          (update-subroot-mapping)
          (retry))))))

(defun make-node->subroot-table ()
  (tg:make-weak-hash-table
   :test 'eq
   :weakness :key
   :size +node->subroot/initial-size+))

(defun compute-node->subroot (node &key (table (make-node->subroot-table)) force)
  "Recurse over NODE, computing a table from NODEs to their dominating subroots."
  (when force
    (clrhash table))
  (let ((first-time (= 0 (hash-table-count table))))
    ;; Using `with-boolean' means we only actually dispatch once on
    ;; `first-time' outside the loop, so we aren't paying for needless
    ;; lookups on the first computation.
    (with-boolean (first-time)
      (let ((live-subroots
              (:if first-time
                   +empty-hash-table+
                   (make-hash-table :test 'eq))))
        (labels ((delete-dead-subroots ()
                   (boolean-unless first-time
                     (iter (for (node subroot) in-hashtable table)
                           (unless (@ live-subroots subroot)
                             (remhash node table)))))
                 (compute-node->subroot (node subroot)
                   (declare (optimize (debug 0))) ;tail recursion
                   (let ((node
                           (if (typep node 'node) node
                               (fset:convert 'node node))))
                     (if (null subroot)
                         (compute-node->subroot node node)
                         (progn
                           (:unless first-time
                             ;; If the subroot hasn't changed, the
                             ;; subroots of the children can't have
                             ;; changed and we don't need to walk them
                             ;; again.
                             (when (subroot? subroot)
                               (let ((old-subroot (@ table node)))
                                 (when (eq old-subroot subroot)
                                   (setf (@ live-subroots subroot) t)
                                   (return-from compute-node->subroot)))))
                           (cond ((and (not (eq node subroot))
                                       (subroot? node))
                                  (when (and subroot (subroot? subroot))
                                    (error "Nested subroots: ~a encloses ~a"
                                           subroot node))
                                  (compute-node->subroot node node))
                                 (t
                                  (setf (@ table node) subroot
                                        (@ live-subroots subroot) t)
                                  (dolist (c (children node))
                                    (compute-node->subroot c subroot)))))))))
          (compute-node->subroot node nil)
          (delete-dead-subroots)
          table)))))

(defun update-subroot-mapping (&optional (attrs *attrs*))
  "Update the node-to-subroot mapping of ATTRS.
This should be done if the root has been mutated."
  (declare (attrs attrs))
  (compute-node->subroot
   (attrs.root attrs)
   :table (attrs.node->subroot attrs))
  attrs)

(defun subroot-map (attrs &key (ensure t))
  "Get the subroot map for ATTRS."
  (let ((root (attrs-root attrs)))
    (assert (slot-exists-p root 'subroot-map))
    (if (slot-boundp root 'subroot-map)
        (let ((value (slot-value root 'subroot-map)))
          (if (typep value 'subroot-map) value
              (setf (slot-value root 'subroot-map)
                    (copy-subroot-map (unbox value)))))
        (and ensure
             (setf (slot-value root 'subroot-map)
                   (make-subroot-map))))))

(defun attrs.subroot->attr-table (attrs &key (ensure t))
  "Get the subroots table for ATTRS.
If ENSURE is non-nil, create the table."
  (when-let (subroot-map (subroot-map attrs :ensure ensure))
    (subroot-map.subroot->attr-table subroot-map)))

(defun attrs.subroot->deps (attrs &key (ensure t))
  "Get the subroot dependencies table for ATTRS.
If ENSURE is non-nil, create the table."
  (when-let (subroot-map (subroot-map attrs :ensure ensure))
    (subroot-map.subroot->deps subroot-map)))

(defun attrs.node->proxy (attrs &key (ensure t))
  "Get the attr proxy table for ATTRS.
If ENSURE is non-nil, create the table."
  (when-let (subroot-map (subroot-map attrs :ensure ensure))
    (subroot-map.node->proxy subroot-map)))

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

(defun attr-proxy (node)
  "Get the attr proxy for NODE.
A node that is not in the tree can have a node in the tree as its
\"attribute proxy\".

This is useful for when, say, we need to answer a query with a node,
but the actual node in the tree is somehow unsuitable. We can return a
node proxied into the tree instead."
  (lret ((proxy (@ (attrs.node->proxy *attrs*) node)))
    (when (and proxy *enable-cross-session-cache*)
      (unless (reachable? proxy :use-cache t)
        (error "Proxy ~a of node ~a is unreachable"
               proxy node)))))

(defun (setf attr-proxy) (proxy node)
  (let* ((attrs *attrs*)
         (root (attrs-root attrs))
         (node->proxy (attrs.node->proxy *attrs*))
         (node->subroot (attrs.node->subroot *attrs*))
         (proxy-subroot (@ node->subroot proxy)))
    (update-subroot-mapping attrs)
    (when (eq proxy node)
      (error "Node ~a and proxy ~a are the same" node proxy))
    (when (@ node->proxy proxy)
      (error "Proxy ~a has a proxy!" proxy))
    (when (reachable? node :proxy nil :from root)
      (error "Cannot proxy ~a: already in tree" node))
    (unless proxy-subroot
      (error "Proxy ~a not in tree" proxy))
    (when (rpath-to-node node proxy)
      (error "Node ~a contains its proxy: ~a" node proxy))
    ;; If we are proxying to another subroot, the proxied node might
    ;; be recorded somewhere, making the proxy subroot an implicit
    ;; dependency of whatever attribute we're calculating.
    (record-deps proxy :current-subroot proxy-subroot :root root)
    ;; It would be surprising to pull out parts of NODE and find later
    ;; they have no connection to PROXY. So all descendants of NODE
    ;; implicitly inherit PROXY (unless they have one already). We
    ;; (probably?) don't need to repeat the validity checks for every
    ;; descendant, though.
    (labels ((set-proxy (node)
               (ensure-gethash node node->proxy proxy)
               (mapc #'set-proxy (children node))))
      (set-proxy node)))
  proxy)

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
                   (reachable? root :from (attrs-root *attrs*)))
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
    ;; The session is "new" if the root was unknown. But it could
    ;; still have a subroot map attached. If so, make sure it's up to
    ;; date.
    (when (and cache new)
      (invalidate-subroots *attrs*))
    (funcall fn)))

(defun delete-dead-proxies (attrs)
  (update-subroot-mapping)
  (let ((node->proxy (attrs.node->proxy attrs))
        (node->subroot (attrs.node->subroot attrs)))
    (iter (for (node proxy) in-hashtable node->proxy)
          ;; Delete proxies that no longer point into the tree.
          (unless (@ node->subroot proxy)
            (remhash node node->proxy))
          ;; Delete proxies that have been inserted into the tree.
          (when (@ node->subroot node)
            (remhash node node->proxy)))))

(defun invalidate-subroots (attrs)
  (delete-dead-proxies attrs)
  (let ((subroot->attr-table (attrs.subroot->attr-table attrs))
        (subroot->deps (attrs.subroot->deps attrs))
        (node->subroot (attrs.node->subroot attrs))
        (removed '()))
    (when (and subroot->attr-table subroot->deps)
      ;; Remove unreachable subroots from the table.
      (iter (for (subroot nil) in-hashtable subroot->attr-table)
            ;; Cheap reachability check.
            (for reachable? = (gethash subroot node->subroot))
            (unless reachable?
              (remhash subroot subroot->attr-table)
              (remhash subroot subroot->deps)
              (push subroot removed)))
      ;; Recursively uncache any subroot that depends on an
      ;; unreachable subroot.
      (iter (for newly-removed-count =
                 (iter (for (subroot deps) in-hashtable subroot->deps)
                       (when (iter (for ptr in deps)
                                   (for dep = (tg:weak-pointer-value ptr))
                                   (thereis
                                    (or (null dep) ;Already GC'd.
                                        (not (gethash dep subroot->attr-table)))))
                         (remhash subroot subroot->deps)
                         (remhash subroot subroot->attr-table)
                         (pushnew subroot removed)
                         (sum 1))))
            (until (zerop newly-removed-count))))
    removed))

(defun record-deps (node &key
                           (current-subroot (current-subroot node))
                           (root (attrs-root*))
                           (subroot-stack *subroot-stack*))
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
         (let ((*subroot-stack* (list root)))
           (funcall fn)))
        (t
         (let* ((current-subroot (current-subroot node))
                (*subroot-stack*
                  (if (subroot? current-subroot)
                      (adjoin current-subroot *subroot-stack*)
                      ;; If there is no subroot but there is a subroot
                      ;; stack, that also means we're computing
                      ;; top-down and should mask the subroot stack.
                      (list root))))
           (when current-subroot
             (unless (or (subroot? current-subroot)
                         (typep current-subroot 'attrs-root))
               (break)
               ;; (print current-subroot)
               ))
           (record-deps node
                        :current-subroot current-subroot
                        :root root)
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
                       (cached-attr-fn ,node nil ',name))
                  body)))
         ,@methods))))

(defun retrieve-memoized-attr-fn (node orig-node fn-name table)
  "Look up memoized value for FN-NAME on NODE.
Return the node's alist, and the pair for FN-NAME if the alist has
one.

If NODE is a proxy, ORIG-NODE should be the original node."
  (declare ((or null node) orig-node))
  (let ((alist (gethash node table)))
    (iter (for p in alist)
          (when (eql (car p) fn-name)
            (etypecase (cdr p)
              (list (return-from retrieve-memoized-attr-fn (values alist p)))
              (t
               (assert (eql (cdr p) :in-progress))
               (error 'circular-attribute
                      :fn fn-name
                      :node (or orig-node node)
                      :proxy (and orig-node node))))))
    (values alist nil)))

(defun cached-attr-fn (node orig-node fn-name)
  "Retrieve the cached value of FN-NAME on NODE, trying the ATTR-MISSING
function on it if not found at first."
  (declare (type function))
  (assert-attrs-bound fn-name)
  (let* ((table (node-attr-table node)))
    (multiple-value-bind (alist p)
        (retrieve-memoized-attr-fn node orig-node fn-name table)
      (when p
        (return-from cached-attr-fn
          (values-list (cdr p))))
      (attr-missing fn-name node)
      (setf (values alist p)
            (retrieve-memoized-attr-fn node orig-node fn-name table))
      (if p
          (values-list (cdr p))
          ;; We tried once, it's still missing, so fail
          (block nil
            (when-let (proxy (attr-proxy node))
              (ignore-some-conditions (uncomputed-attr)
                (return (cached-attr-fn proxy node fn-name))))
            ;; The proxy also failed.
            (error (make-condition 'uncomputed-attr :node node :fn fn-name)))))))

(defun memoize-attr-fun (node fn-name thunk)
  "Look for a memoized value for attr function FN-NAME on NODE.
If not there, invoke the thunk THUNK and memoize the values returned."
  (declare (type function thunk))
  (assert-attrs-bound fn-name)
  (let* ((orig-node node)
         (proxy (attr-proxy node))
         (node (or proxy node))
         (table (node-attr-table node))
         (in-progress :in-progress))
    (multiple-value-bind (alist p)
        (retrieve-memoized-attr-fn node (and proxy orig-node) fn-name table)
      (when p
        (typecase (cdr p)
          (list (return-from memoize-attr-fun (values-list (cdr p))))
          (t
           (assert (eql (cdr p) in-progress))
           (error 'circular-attribute :node orig-node
                                      :proxy proxy
                                      :fn fn-name))))
      (let* ((p (cons fn-name in-progress))
             (trail-pair (cons fn-name node))
             (*attribute-trail*
               (cons trail-pair *attribute-trail*)))
        (declare (dynamic-extent trail-pair *attribute-trail*))
        ;; additional pushes onto the alist may occur in the call to THUNK,
        ;; so get the push of p onto the list out of the way now.  If we
        ;; tried to assign after the call we might lose information.
        (unwind-protect
             (progn
               (when proxy
                 (record-deps proxy))
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

(define-condition attribute-condition (condition)
  ())

(define-condition attribute-error (error attribute-condition)
  ())

(define-condition node-attribute-error (attribute-error)
  ((node :initarg :node :reader attribute-error-node)
   (fn :initarg :fn :reader attribute-error-function)))

(define-condition circular-attribute (node-attribute-error)
  ((node :initarg :node :reader circular-attribute-node)
   (proxy :initarg :proxy :reader circular-attribute-proxy)
   (fn :initarg :fn :reader circular-attribute-function)
   (trail :initarg :trail :reader circular-attribute-trail))
  (:default-initargs
   :proxy nil
   ;; NB *attribute-trail* is stack-allocated.
   :trail (copy-tree *attribute-trail*))
  (:report
   (lambda (c s)
     (with-slots (node proxy fn trail) c
       (let ((*print-circle* nil))
         (format s
                 "Circularity detected in attribute ~a on ~a~@[ (proxy ~a)~]~%Trail (deepest first):~%~{~a~%~}"
                 fn node proxy
                 (cons (cons fn node)
                       trail)))))))

(define-condition uncomputed-attr (node-attribute-error)
  ((node :reader uncomputed-attr-node)
   (fn :reader uncomputed-attr-function))
  (:report (lambda (condition stream)
             (format stream "Uncomputed attr function ~a on node ~a (~s did not work)~%Present in tree: ~:[NO~;YES~]"
                     (uncomputed-attr-function condition)
                     (uncomputed-attr-node condition)
                     'attr-missing
                     (let* ((root (fset:convert 'node (attrs-root*)))
                            (node (uncomputed-attr-node condition))
                            (path (path-of-node root node)))
                       (and path (eql (fset:lookup root path) node)))))))

(defun assert-attrs-bound (fn-name)
  (unless (boundp '*attrs*)
    (error (make-condition 'unbound-attrs :fn-name fn-name))))

(define-condition unbound-attrs (unbound-variable attribute-error)
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

(define-condition unreachable-node (attribute-error)
  ((root :initarg :root)
   (node :initarg :node))
  (:report
   (lambda (c s)
     (with-slots (root node) c
       (format s "~a is not reachable from ~a" node root)))))

(define-condition session-shadowing (attribute-error)
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
    (and-let* ((node (or (attr-proxy node) node))
               (table (node-attr-table node))
               (alist (gethash node table)))
      (if attr-name-supplied-p
          (assoc attr-name alist)
          alist))))
