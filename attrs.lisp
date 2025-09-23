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
    :equal?
    :mapc
    :mapcar
    :subst
    :subst-if
    :subst-if-not)
  (:import-from
    :serapeum
    :->
    :@
    :and-let*
    :assure
    :boolean-if
    :boolean-unless
    :bound-value
    :box
    :boxp
    :callf
    :def
    :defconst
    :defparameter-unbound
    :defplace
    :defstruct-read-only
    :defsubst
    :defvar-unbound
    :do-each
    :econd
    :etypecase-of
    :lret
    :mvlet*
    :nest
    :nlet
    :pop-assoc
    :slot-value-safe
    :unbox
    :standard/context
    :vect
    :with-boolean
    :with-thunk)
  (:export
    :*approximation*
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
    :finalize-approximation
    :handle-circular-attribute
    :has-attribute-p
    :invalidate-subroot
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


;;; Memoized values

(defvar *allow-circle* t
  "Whether to allow circular attributes.")

(defvar *circle* nil
  "The currently executing circular attribute evaluation, if any.")

(defparameter *max-circular-iterations* 100)

(defgeneric attribute-bottom (attr)
  (:documentation
   "Return the bottom value for a circular attribute.
This can return multiple values.")
  (:method ((attr t))
    (values)))

(defgeneric attribute-converged-p (attr old new)
  (:documentation
   "Return true if OLD and NEW have converged.")
  (:method ((attr t) x y)
    (equal x y)))

(defclass circular-eval ()
  ((changep
    :documentation "Has there been a change in this iteration?"
    :initform nil
    :type boolean)
   (iteration
    :reader circle-iteration
    :documentation "How many iterations have been performed?"
    :initform 0
    :type (integer 0))
   (max-visit-count
    :documentation "Count the max number of accesses"
    :accessor max-visit-count
    :initform 0)
   (memo-cells
    :accessor memo-cells
    :documentation "Holds memo cells to memoize when done."
    :initform (vect)
    :type vector))
  (:documentation "Circular evaluation state"))

(defvar *approximation* nil)

(def +final-value+ -1)
(deftype iteration ()
  'fixnum)

(declaim (inline approximation))
(defstruct (approximation
            (:constructor approximation
                (&optional values visiting-p)))
  "Holds the approximation to attributes during circular evaluation."
  (values nil :type list)
  (visiting-p nil :type boolean)
  ;; The overall cycle iteration where the value was last computed.
  ;; Tracked to avoid evaluating the same cycle more than once. NB
  ;; iteration 0 never actually happens.
  (iteration 0 :type iteration)
  (visit-count 0 :type (unsigned-byte 32)))

(defun finalize-approximation ()
  "Mark the approximation currently being computed as having converged."
  (when-let (a *approximation*)
    (setf (approximation-iteration a) +final-value+)))

(defsubst approximation-finalized-p (a)
  (eql (approximation-iteration a) +final-value+))

(deftype memoized-value ()
  "Type of a attribute value: either an approximation, or a list of the
values returned by the attribute function."
  '(or approximation list))

(deftype memo-cell ()
  '(cons symbol memoized-value))

(declaim
 (inline
  cell-attr
  cell-data
  cell-values
  (setf cell-attr)
  (setf cell-data)
  (setf cell-values)))

(defplace cell-attr (memo-cell)
  "Return the attribute of MEMO-CELL."
  (car memo-cell))

(defplace cell-data (memo-cell)
  "Return the data of MEMO-CELL (an approximation or a list of values)."
  (cdr memo-cell))

(defun cell-values (memo-cell)
  (let ((data (cell-data memo-cell)))
    (etypecase-of memoized-value data
      (approximation (approximation-values data))
      (list (values-list data)))))

(defun (setf cell-values) (values memo-cell)
  (declare (list values))
  (with-accessors ((data cell-data)) memo-cell
    (etypecase-of memoized-value data
      (approximation (setf (approximation-values data) values))
      (list (setf data values)))))

(defun mark-visiting (memo-cell &aux (circle *circle*))
  (declare (memo-cell memo-cell))
  (with-accessors ((visiting-p approximation-visiting-p)
                   (visit-count approximation-visit-count))
      (cell-data memo-cell)
    (setf visiting-p t)
    (incf visit-count)
    (when circle
      (maxf (max-visit-count circle)
            visit-count))))

(defun mark-not-visiting (memo-cell)
  (declare (memo-cell memo-cell))
  (setf (approximation-visiting-p (cell-data memo-cell)) nil))

(defun call/visit (memo-cell body-fn)
  (let ((visiting-initially-p
          (approximation-visiting-p (cell-data memo-cell))))
    (mark-visiting memo-cell)
    (multiple-value-prog1 (funcall body-fn)
      (setf (approximation-visiting-p (cell-data memo-cell))
            visiting-initially-p))))

(defmacro with-visit ((memo-cell) &body body)
  (with-thunk (body)
    `(call/visit ,memo-cell ,body)))


;;; Attribute sessions.

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
                          (&key (subroot->attr-table (make-weak-node-table))
                             (subroot->deps (make-weak-node-table))
                             (node->proxy (make-weak-node-table)))))
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

(defstruct (cow-table
            (:conc-name cow-table.)
            (:copier nil))
  "COW (copy-on-write) wrapper for a hash table."
  (hash-table (make-weak-node-table) :type hash-table)
  (hash-table-copied-p nil :type boolean))

(defun cow-table.on-write (cow-table)
  "Do the actual on-write copy."
  (unless (cow-table.hash-table-copied-p cow-table)
    (callf #'copy-weak-node-table (cow-table.hash-table cow-table))
    (setf (cow-table.hash-table-copied-p cow-table) t))
  cow-table)

(defun copy-cow-table (cow-table)
  "Copy COW-TABLE without copying the wrapped hash table."
  (make-cow-table
   :hash-table (cow-table.hash-table cow-table)
   :hash-table-copied-p nil))

(defun cow-table.ref (cow-table key)
  "Lookup KEY in COW-TABLE's wrapped hash table."
  (gethash key (cow-table.hash-table cow-table)))

(defun ref (table key)
  "Lookup KEY in a COW table or a bare hash table."
  (etypecase table
    (hash-table
     (gethash key table))
    (cow-table
     (cow-table.ref table key))))

(defun (setf cow-table.ref) (value cow-table key)
  "Set KEY to VALUE in COW-TABLE's wrapped hash table."
  (symbol-macrolet ((ht (cow-table.hash-table cow-table)))
    (if (eq value (@ ht key))
        ;; Optimization: don't copy if the value is the same.
        value
        (progn
          (cow-table.on-write cow-table)
          (setf (@ ht key) value)))))

(defun (setf ref) (value table key)
  "Set KEY to VALUE in TABLE, a COW table or bare hash table."
  (etypecase table
    (hash-table
     (setf (gethash key table) value))
    (cow-table
     (setf (cow-table.ref table key) value))))

(defun copy-subroot->attr-table (table)
  "Copy the table from subroots to attr tables, ensuring each attr
table is a fresh table."
  (lret ((table (copy-weak-node-table table)))
    (iter (for (subroot attr-table) in-hashtable table)
          (setf (@ table subroot)
                (copy-cow-table attr-table)))))

(-> copy-subroot-map (subroot-map) subroot-map)
(defun copy-subroot-map (map)
  "Copy MAP and its constituent tables.
The new subroot map should be fully independent of MAP."
  (make-subroot-map
   :subroot->attr-table
   (copy-subroot->attr-table (subroot-map.subroot->attr-table map))
   :subroot->deps (copy-weak-node-table (subroot-map.subroot->deps map))
   :node->proxy (copy-weak-node-table (subroot-map.node->proxy map))))

(defstruct-read-only (attrs
                      (:conc-name attrs.)
                      (:constructor make-attrs
                          (root &aux (node->subroot
                                      (if *enable-cross-session-cache*
                                          (compute-node->subroot root)
                                          (make-node->subroot-table))))))
  "An attribute session.
This holds at least the root of the attribute computation."
  (root :type attrs-root)
  ;; This is only used if *enable-cross-session-cache* is nil.
  (table (make-weak-node-table) :type hash-table)
  (cachep *enable-cross-session-cache* :type boolean)
  ;; Pre-computed table from nodes to their subroots.
  (node->subroot :type hash-table))

(defsubst attrs-root (attrs)
  (attrs.root attrs))

(defsubst attrs-root* ()
  "Get the root of the current attrs table."
  (attrs-root *attrs*))

(defmethod fset:convert ((to (eql 'node)) (attrs attrs) &key)
  (attrs-root attrs))


;;; Subroot implementation

(defun make-weak-node-table (&rest args)
  "Make a weak 'eq hash table."
  (multiple-value-call #'make-weak-hash-table
    :weakness :key
    :test #'eq
    (values-list args)))

(defun copy-weak-node-table (table-in &rest args)
  "Copy a weak 'eq hash table."
  (let ((table-out (apply #'make-weak-node-table :size (hash-table-size table-in) args)))
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
           (multiple-value-bind (rpath node-found)
               (rpath-to-node real-root real-node)
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
                 ;; There's something at that path, but not this
                 ;; identical node.
                 (when (eql node node-found)
                   (find-if #'subroot? rpath))))))))

(defun reachable-in-attrs? (node &key (proxy t))
  "Does NODE have a subroot (or a proxy) recorded in the current
attribute tables?"
  (when-let (attrs (bound-value '*attrs*))
    (let ((node->subroot (attrs.node->subroot attrs))
          (node (fset:convert 'node node)))
      (or (@ node->subroot node)
          (when-let (proxy (and proxy (attr-proxy node)))
            (@ node->subroot proxy))))))

(defun reachable-from-root? (root dest &key (proxy t))
  "Is DEST reachable from ROOT? This is careful to check not just if
DEST has a path, but if DEST is the node at that path."
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
                          use-attrs
                          (from (attrs-root*)))
  (if use-attrs
      (or (reachable-in-attrs? dest :proxy proxy)
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
  (let ((first-time (= 0 (hash-table-count table)))
        (live-subroots (make-hash-table :test 'eq)))
    ;; Using `with-boolean' means we only actually dispatch once on
    ;; `first-time' outside the loop, so we aren't paying for needless
    ;; lookups on the first computation.
    (with-boolean (first-time)
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
                         (boolean-unless first-time
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
                                  (error 'nested-subroots
                                         :outer subroot
                                         :inner node))
                                (compute-node->subroot node node))
                               (t
                                (setf (@ table node) subroot
                                      (@ live-subroots subroot) t)
                                (dolist (c (children node))
                                  (compute-node->subroot c subroot)))))))))
        (compute-node->subroot node nil)
        (delete-dead-subroots)
        table))))

(defun update-subroot-mapping (&optional (attrs *attrs*))
  "Update the node-to-subroot mapping of ATTRS.
This should be done if the root has been mutated."
  (declare (attrs attrs))
  (compute-node->subroot
   (attrs.root attrs)
   :table (attrs.node->subroot attrs))
  attrs)

(defun ensure-subroot-map (attrs)
  "Ensure a subroot map for ATTRS.
This implements the subroot map copy-on-write behavior: after this
function is called, the root of ATTRs will have its own subroot map."
  (let ((root (attrs-root attrs)))
    (assert (slot-exists-p root 'subroot-map))
    (with-slots (subroot-map) root
      (if (slot-boundp root 'subroot-map)
          (if (typep subroot-map 'subroot-map)
              subroot-map
              (setf subroot-map
                    (copy-subroot-map (unbox subroot-map))))
          (setf subroot-map (make-subroot-map))))))

(defsubst attrs.subroot->attr-table (attrs)
  "Ensure the subroots table for ATTRS."
  (subroot-map.subroot->attr-table (ensure-subroot-map attrs)))

(defsubst attrs.subroot->deps (attrs)
  "Ensure the subroot dependencies table for ATTRS."
  (subroot-map.subroot->deps (ensure-subroot-map attrs)))

(defsubst attrs.node->proxy (attrs)
  "Ensure the attr proxy table for ATTRS."
  (subroot-map.node->proxy (ensure-subroot-map attrs)))

(defun node-attr-table (node)
  (if *enable-cross-session-cache*
      (cow-table (current-subroot node))
      (attrs.table *attrs*)))

(defun cow-table (subroot)
  "Get the attr table for SUBROOT in the current session.
This implements copy-on-write logic."
  (ensure-gethash subroot
                  (attrs.subroot->attr-table *attrs*)
                  (make-cow-table)))

(defun subroot-deps (subroot)
  "Get the dependencies of SUBROOT in the current session."
  (gethash subroot (attrs.subroot->deps *attrs*)))

(defun (setf subroot-deps) (value subroot)
  (setf (gethash subroot (attrs.subroot->deps *attrs*))
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
      (unless (reachable? proxy :use-attrs t)
        (error 'unreachable-proxy
               :root (attrs-root*)
               :proxy proxy
               :node node)))))

(defun (setf attr-proxy) (proxy node)
  (let* ((attrs *attrs*)
         (root (attrs-root attrs))
         (node->proxy (attrs.node->proxy *attrs*))
         (node->subroot (attrs.node->subroot *attrs*))
         (proxy-subroot
           (progn
             ;; Update the subroot mapping before querying it.
             (update-subroot-mapping attrs)
             (@ node->subroot proxy))))
    (when-let (real-proxy (@ node->proxy proxy))
      (when (@ node->proxy real-proxy)
        ;; This shouldn't be possible.
        (error 'proxy-has-proxy
               :node node
               :proxy proxy))
      (return-from attr-proxy
        (setf (attr-proxy node) real-proxy)))
    ;; Can't proxy a node with a proxy.
    ;; A node can't proxy itself.
    (when (eq proxy node)
      (error 'self-proxy
             :proxy proxy
             :node node))
    ;; Proxying a node already in the tree would be useless.
    (when (reachable? node :proxy nil :from root)
      (error 'useless-proxy
             :node node
             :proxy proxy))
    ;; A node that's not in the tree can't be a proxy.
    (unless proxy-subroot
      (error 'unreachable-proxy
             :root (attrs-root*)
             :node node
             :proxy proxy))
    ;; The node must not contain its proxy. (See below on proxying the
    ;; descendants of a node.)
    (when (rpath-to-node node proxy)
      (error 'node-contains-proxy
             :node node
             :proxy proxy))
    ;; If we are proxying to another subroot, the proxied node might
    ;; be recorded somewhere, making the proxy subroot an implicit
    ;; dependency of whatever attribute we're calculating.
    (record-deps proxy :current-subroot proxy-subroot :root root)
    ;; It would be surprising to pull out parts of NODE and find later
    ;; they have no connection to PROXY. So all descendants of NODE
    ;; implicitly inherit PROXY (unless they have one already).
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
                (setf new t)))))
         (*circle*
           ;; Don't continue cycles in the outer attribute session.
           (if shadow nil *circle*)))
    (unless (eql cache (attrs.cachep *attrs*))
      (error 'incompatible-cache-option))
    ;; The session is "new" if the root was unknown. But it could
    ;; still have a subroot map attached. If so, make sure it's up to
    ;; date.
    (when (and cache new)
      (invalidate-subroots *attrs*))
    (funcall fn)))

(defun delete-invalid-proxies (attrs)
  "Delete any invalid node->proxy mappings.
Node-to-proxy mappings are invalid when the proxy is no longer in the
tree, or when the node itself has been inserted into the tree."
  (update-subroot-mapping)
  (let ((node->proxy (attrs.node->proxy attrs))
        (node->subroot (attrs.node->subroot attrs)))
    (iter (for (node proxy) in-hashtable node->proxy)
          ;; Delete proxies that no longer point into the tree.
          (unless (@ node->subroot proxy)
            (remhash node node->proxy))
          ;; Delete proxies for nodes that have been inserted into the
          ;; tree.
          (when (@ node->subroot node)
            (remhash node node->proxy)))))

(defun invalidate-subroots (attrs)
  "Recursively invalidate subroots in ATTRS.
Invalid subroots are either unreachable subroots, or
depend on invalid subroots."
  (delete-invalid-proxies attrs)
  (let ((subroot->attr-table (attrs.subroot->attr-table attrs))
        (subroot->deps (attrs.subroot->deps attrs))
        (node->subroot (attrs.node->subroot attrs))
        (removed (fset:empty-set)))
    (when (and subroot->attr-table subroot->deps)
      ;; Remove unreachable subroots from the table.
      (iter (for (subroot nil) in-hashtable subroot->attr-table)
            ;; Cheap reachability check.
            (for reachable? = (gethash subroot node->subroot))
            (unless reachable?
              (remhash subroot subroot->attr-table)
              (remhash subroot subroot->deps)
              (callf #'fset:with removed subroot)))
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
                         (callf #'fset:with removed subroot)
                         (sum 1))))
            (until (zerop newly-removed-count))))
    removed))

(defun invalidate-subroot (subroot &key (attrs (bound-value '*attrs*)))
  "Invalidate attributes on SUBROOT.
This should be used if SUBROOT is mutated."
  (when attrs
    (remhash subroot (attrs.subroot->attr-table attrs))
    subroot))

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
         (let ((*subroot-stack* nil))
           (funcall fn)))
        (t
         (let* ((current-subroot (current-subroot node))
                (*subroot-stack*
                  (if (subroot? current-subroot)
                      (adjoin current-subroot *subroot-stack*)
                      ;; If there is no subroot but there is a subroot
                      ;; stack, that also means we're computing
                      ;; top-down and should mask the subroot stack.
                      nil)))
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
  "Define an attribute.
The attribute function is always at least arity 1, the node whose
attribute is being computed; if OPTIONAL-ARGS are provided they are
the inputs for the attribute computation (e.g. in the symbol table,
the symbol tables of parents or prior siblings).

Attribute functions without OPTIONAL-ARGS are \"synthesized\"
attributes; attribute functions with OPTIONAL-ARGS are \"inherited\"
attributes.

If you are defining an inherited attribute you may also want to
specialize `attr-missing' to restart the computation of the attribute
from the root node, if it has not been computed for the node passed in
here.

To define a circular attribute, supply the `(:circular)' option with
two arguments.. The first argument is the converge test; the second
value is a function to call to get the bottom value \(defaults to
`nil' if not provided). Both arguments are evaluated in the lexical
environment of the point of definition.. You can return multiple
values in the bottom thunk, but returning no values means an attribute
will not be considered circular.

    ;; The attribute returns two values as its bottom. `fset:equal?`
    ;; will be used to compare the values to see if they've converged.
    (:circular #'fset:equal? (lambda () (values (empty-map) (empty-set))))

Since only attributes defined as circular can participate in a cycle
(a non-circular attribute in a cycle starts a new, distinct
sub-cycle), and the overhead for a potentially-circular attribute
outside of an actual cycle is minimal, it's desirable to declare
attributes circular whenever that makes sense. However the equality
predicate and bottom value or values must still be specified on a
per-attribute basis."
  (assert (symbolp name))
  (assert (every #'symbolp optional-args))
  (with-gensyms (node present?)
    (mvlet*
        ((docstring
          (when (stringp (car methods))
            (pop methods)))
         (body
          (let ((body '((call-next-method))))
            (with-thunk (body)
              `(memoize-attr-fun ,node ',name ,body))))
         (circular
          (pop-assoc :circular methods))
         (test bottom
          (when circular
            (destructuring-bind (test bottom)
                (rest circular)
              (values test bottom)))))
      (with-unique-names (bottom-val test-val)
        `(progn
           ;; These are always defined so they are overridden if the
           ;; attribute is redefined to be noncircular.
           ,(if circular
                `(let ((,bottom-val (ensure-function ,bottom)))
                   (defmethod attribute-bottom ((attr (eql ',name)))
                     (funcall ,bottom-val)))
                `(defmethod attribute-bottom ((attr (eql ',name)))
                   (values)))
           ,(if circular
                `(let ((,test-val (ensure-function ,test)))
                   (defmethod attribute-converged-p ((attr (eql ',name)) old new)
                     (funcall ,test-val old new)))
                `(defmethod attribute-converged-p ((attr (eql ',name)) old new)
                   (declare (ignore old new))
                   (call-next-method)))
           (defgeneric ,name (,node ,@(when optional-args `(&optional ,@optional-args)))
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
             ,@methods))))))

(defun retrieve-memoized-attr-fn (node fn-name table)
  "Look up memoized value for FN-NAME on NODE.
Return the node's alist, and the memo cell for FN-NAME if the alist
has one.

If NODE is a proxy, ORIG-NODE should be the original node."
  (let* ((alist (ref table node)))
    (values alist (assoc fn-name alist))))

(defun cached-attr-fn (node fn-name &key)
  "Retrieve the cached value of FN-NAME on NODE, trying the ATTR-MISSING
function on it if not found at first."
  (declare (type function))
  (check-attrs-bound fn-name)
  (let* ((table (node-attr-table node)))
    (multiple-value-bind (alist p)
        (retrieve-memoized-attr-fn node fn-name table)
      (when p
        (etypecase-of memoized-value (cdr p)
          (list
           (return-from cached-attr-fn
             (values-list (cdr p))))
          (approximation
           (return-from cached-attr-fn
             (values-list (approximation-values (cdr p)))))))
      (attr-missing fn-name node)
      (setf (values alist p)
            (retrieve-memoized-attr-fn node fn-name table))
      (if p
          (etypecase-of memoized-value (cdr p)
            (list
             (values-list (cdr p)))
            (approximation
             (values-list (approximation-values (cdr p)))))
          ;; We tried once, it's still missing, so fail
          (block nil
            (when-let (proxy (attr-proxy node))
              (ignore-some-conditions (uncomputed-attr)
                (return (cached-attr-fn proxy fn-name))))
            ;; The proxy also failed.
            (error (make-condition 'uncomputed-attr :node node :fn fn-name)))))))

(defun values-converged-p (fn-name xs ys)
  (and (length= xs ys)
       (every
        (lambda (x y)
          (attribute-converged-p fn-name x y))
        xs ys)))

(defun memoize-attr-fun (node fn-name thunk)
  "Look for a memoized value for attr function FN-NAME on NODE.
If not there, invoke the thunk THUNK and memoize the values returned."
  (declare (type function thunk))
  (check-attrs-bound fn-name)
  (nest
   (let* ((proxy (attr-proxy node))
          (node (or proxy node))
          (table (node-attr-table node))))
   (multiple-value-bind (alist cell)
       (retrieve-memoized-attr-fn
        node
        fn-name
        table))
   (if (and cell (listp (cell-data cell)))
       ;; Already final.
       (values-list (cell-data cell)))
   ;; Stack of attributes being computed.
   (let* ((trail-pair (cons fn-name node))
          (*attribute-trail*
            (cons trail-pair *attribute-trail*))
          ;; Bottom values for the fixed point computation.
          (bottom-values
            (multiple-value-list (attribute-bottom fn-name)))
          ;; Flag to track exit kind.
          normal-exit)
     (declare (dynamic-extent trail-pair *attribute-trail*))
     (when proxy
       (record-deps proxy))
     (unless cell
       ;; additional pushes onto the alist may occur in the call to
       ;; THUNK, so get the push of p onto the list out of the way
       ;; now. If we tried to assign after the call we might lose
       ;; information.
       (setf cell
             (cons fn-name (approximation bottom-values))
             (ref table node)
             (cons cell alist))
       (when *circle*
         (vector-push-extend cell (memo-cells *circle*))))
     table)
   (with-accessors ((cell-data cell-data)) cell)
   (labels ((convergedp (xs ys)
              (values-converged-p fn-name xs ys))
            (approximation-changed-p (a &aux changep)
              (with-accessors ((old-vals approximation-values)) a
                (if (approximation-finalized-p a)
                    (values-list old-vals)
                    (let ((new-vals
                            (let ((*approximation* a))
                              (multiple-value-list (funcall thunk)))))
                      (unless (convergedp new-vals old-vals)
                        (setf changep t
                              old-vals new-vals)))))
              changep)))
   (unwind-protect
        ;; This implements the evaluation strategy for circular
        ;; attributes from Magnusson 2007.
        (multiple-value-prog1
            (econd
              ((listp cell-data)
               (values-list cell-data))
              ;; TODO Should we distinguish "agnostic" attributes (that
              ;; allow circular eval, but don't require it) from
              ;; noncircular attributes (that always start a new
              ;; subgraph?) Cf. Öqvist 2017.
              ((not (and bottom-values *allow-circle*))
               (when (approximation-visiting-p cell-data)
                 (error 'circular-attribute
                        :node node
                        :proxy proxy
                        :fn fn-name))
               (mark-visiting cell)     ;unbalanced
               (values-list
                (if *circle*
                    ;; Start a new circular eval (SCC).
                    (let ((*circle* nil))
                      (setf cell-data
                            (multiple-value-list (funcall thunk))))
                    (setf cell-data
                          (multiple-value-list (funcall thunk))))))
              ((approximation-finalized-p cell-data)
               (setf cell-data (approximation-values cell-data))
               (values-list cell-data))
              ((not *circle*)
               (let*
                   ;; `*circle*' distinguishes whether we are in a
                   ;; circle, and tracks the approximated attributes
                   ;; so we can memoize them once we've reached a
                   ;; fixed point. It also tracks the max number of
                   ;; times any node has actually been visited, so we
                   ;; know if evaluation was actually circular. Note
                   ;; this does mean we may be evaluating cycles in
                   ;; other SCCs of the attribute graph; we do start
                   ;; new cycles when we encounter a definitely
                   ;; noncircular attribute.
                   ((circle (make-instance 'circular-eval))
                    (*circle* circle)
                    (max-iterations *max-circular-iterations*))
                 (with-slots (changep
                              iteration
                              max-visit-count
                              memo-cells)
                     circle
                   (vector-push-extend cell memo-cells)
                   (iter
                     (when (>= (incf iteration) max-iterations)
                       (error "Divergent attribute after ~a iteration~:p: ~s"
                              max-iterations
                              fn-name))
                     (setf changep nil)
                     (setf (approximation-iteration cell-data) iteration)
                     (mark-visiting cell) ;Unbalanced.
                     (when (approximation-changed-p cell-data)
                       (setf changep t))
                     (while (and changep
                                 ;; If no attribute is accessed more
                                 ;; than once, the attribute is not
                                 ;; actually circular.
                                 (> max-visit-count 1))))
                   (mark-not-visiting cell)
                   (setf (approximation-iteration cell-data)
                         +final-value+)
                   ;; We've reached a fixed point, memoize the
                   ;; approximations.
                   (do-each (c memo-cells)
                     (when (approximation-p (cell-data c))
                       (setf (cell-data c)
                             (approximation-values (cell-data c)))))
                   (values-list cell-data))))
              ((not (eql (circle-iteration *circle*)
                         (approximation-iteration cell-data)))
               (let ((circle *circle*))
                 (with-slots (changep iteration) circle
                   (setf (approximation-iteration cell-data)
                         iteration)
                   (with-visit (cell)
                     (when (approximation-changed-p cell-data)
                       (setf changep t))
                     (values-list (approximation-values cell-data))))))
              ((approximation-p cell-data)
               (with-visit (cell)
                 (values-list (approximation-values cell-data)))))
          (setf normal-exit t))
     ;; If a non-local return occured from THUNK, we need
     ;; to remove p from the alist, otherwise we will never
     ;; be able to compute the function here
     (unless normal-exit
       (etypecase-of memoized-value cell-data
         (list)
         (approximation
          (removef (ref table node) cell)))))))

(define-condition attribute-condition (condition)
  ())

(define-condition attribute-error (error attribute-condition)
  ())

(define-condition nested-subroots (attribute-error)
  ((outer :initarg :outer :reader nested-subroots-outer)
   (inner :initarg :inner :reader nested-subroots-inner))
  (:report
   (lambda (c s)
     (with-slots (outer inner) c
       (format s "Nested subroots: ~a contains ~a"
               outer inner)))))

(define-condition node-attribute-error (attribute-error)
  ((node :initarg :node :reader attribute-error-node)
   (fn :initarg :fn :reader attribute-error-function)))

(define-condition attr-proxy-error (node-attribute-error)
  ((node :initarg :node
         :reader attribute-error-node
         :reader attr-proxy-error-node)
   (proxy :initarg :proxy
          :reader attr-proxy-error-proxy)))

(define-condition useless-proxy (attr-proxy-error)
  ()
  (:report
   (lambda (c s)
     (with-slots (node) c
       (format s "Node ~a is already in the tree!"
               node)))))

(define-condition self-proxy (attr-proxy-error)
  ()
  (:report
   (lambda (c s)
     (with-slots (node proxy) c
       (format s "Proxy ~a and node ~a are the same"
               proxy node)))))

(define-condition proxy-has-proxy (attr-proxy-error)
  ()
  (:report
   (lambda (c s)
     (with-slots (proxy) c
       (format s "Proxy ~a has a proxy!"
               proxy)))))

(define-condition node-contains-proxy (attr-proxy-error)
  ()
  (:report
   (lambda (c s)
     (with-slots (node proxy) c
       (format s "Node ~a contains its proxy ~a"
               node proxy)))))

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
                     (reachable? (uncomputed-attr-node condition))))))

(defun check-attrs-bound (fn-name)
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

(define-condition unreachable-proxy (unreachable-node attr-proxy-error)
  ((root :initarg :root)
   (node :initarg :node))
  (:report
   (lambda (c s)
     (with-slots (root proxy) c
       (format s "Proxy ~a is not reachable from ~a"
               proxy root)))))

(define-condition session-shadowing (attribute-error)
  ((outer :initarg :outer)
   (inner :initarg :inner)
   (inherit :initarg :inherit))
  (:report
   (lambda (c s)
     (with-slots (outer inner inherit) c
       (format s "Attempt to shadow attribute session for ~a by~@[ unrelated~:*~] session for ~a"
               outer
               inherit
               inner)))))

(define-condition incompatible-cache-option (attribute-error)
  ()
  (:report
   (lambda (c s)
     (declare (ignore c))
     (format s "Cannot inherit with differing values for caching"))))

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
               (alist (ref table node)))
      (if attr-name-supplied-p
          (assoc attr-name alist)
          alist))))
