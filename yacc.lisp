; Copyright (c) 2005 by Juliusz Chroboczek

; Permission is hereby granted, free of charge, to any person obtaining a copy
; of this software and associated documentation files (the "Software"), to deal
; in the Software without restriction, including without limitation the rights
; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
; copies of the Software, and to permit persons to whom the Software is
; furnished to do so, subject to the following conditions:

; The above copyright notice and this permission notice shall be included in
; all copies or substantial portions of the Software.

; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
; THE SOFTWARE.

(defpackage #:yacc
  (:use #:common-lisp)
  (:export #:make-production #:make-grammar #:make-parser #:parse-with-lexer
           #:define-grammar #:define-parser
           #:yacc-parse-error #:yacc-parse-error-terminal
           #:yacc-parse-error-value #:yacc-parse-error-expected-terminals)
  #+CMU
  (:import-from #:extensions #:required-argument)
  )

(in-package #:yacc)

#-CMU
(defun required-argument () (error "A required argument was not supplied"))

(defun constantly-error (string)
  (declare (string string))
  #'(lambda (&rest ignore)
      (declare (ignore ignore))
      (error string)))

(deftype index () '(unsigned-byte 10))
(deftype signed-index () '(signed-byte 11))

;;; Productions

(defstruct (production
             (:constructor make-production (symbol derives
                                            &key action action-form))
             (:print-function print-production))
  (id nil :type (or null index))
  (symbol (required-argument) :type symbol)
  (derives (required-argument) :type list)
  (action #'list :type function)
  (action-form nil))

(defun print-production (p s d)
  (declare (type production p) (stream s) (ignore d))
  (print-unreadable-object (p s :type t)
    (format s "~S -> ~{~S~^ ~}" (production-symbol p) (production-derives p))))

(declaim (inline production-equal-p))
(defun production-equal-p (p1 p2)
  "Equality predicate for productions within a single grammar"
  (declare (type production p1 p2))
  (eq p1 p2))

(declaim (inline production<))
(defun production< (p1 p2)
  "Total order on productions within a single grammar"
  (declare (type production p1 p2))
  (< (production-id p1) (production-id p2)))

 ;;; Grammars

(defstruct (grammar (:constructor %make-grammar))
  (name nil)
  (terminals '() :type list)
  (productions '() :type list)
  (%symbols :undefined :type (or list (member :undefined)))
  (derives-epsilon '() :type list)
  (derives-first '() :type list)
  (derives-first-terminal '() :type list))

(defun make-grammar(&key name (start-symbol (required-argument))
                    terminals productions)
  (declare (symbol name start-symbol) (list terminals productions))
  (setq productions
        (cons (make-production 's-prime (list start-symbol)
                               :action #'identity :action-form '#'identity)
              productions))
  (do* ((i 0 (+ i 1)) (ps productions (cdr ps)) (p (car ps) (car ps)))
       ((null ps))
    (setf (production-id p) i))
  (%make-grammar :name name :terminals terminals :productions productions))

(defun grammar-discard-memos (grammar)
  (setf (grammar-%symbols grammar) :undefined)
  (setf (grammar-derives-epsilon grammar) '())
  (setf (grammar-derives-first grammar) '())
  (setf (grammar-derives-first-terminal grammar) '()))

(defun terminal-p (symbol grammar)
  (declare (symbol symbol) (type grammar grammar))
  (or (eq symbol 'propagate)
      (and (member symbol (grammar-terminals grammar)) t)))

(defun grammar-symbols (grammar)
  (declare (type grammar grammar))
  (cond
    ((eq :undefined (grammar-%symbols grammar))
     (let ((res '()))
       (dolist (p (grammar-productions grammar))
         (pushnew (production-symbol p) res)
         (dolist (s (production-derives p))
           (pushnew s res)))
       (setf (grammar-%symbols grammar) res)
       res))
    (t (grammar-%symbols grammar))))

(defun grammar-epsilon-productions (grammar)
  (remove-if-not #'(lambda (r) (null (production-derives r)))
                 (grammar-productions grammar)))

(defun derives-epsilon (symbol grammar &optional seen)
  "True if symbol derives epsilon."
  (declare (symbol symbol) (type grammar grammar) (list seen))
  (let ((e (assoc symbol (grammar-derives-epsilon grammar))))
    (cond
      (e (cdr e))
      ((terminal-p symbol grammar) nil)
      ((member symbol seen) nil)
      (t
       (let ((res (derives-epsilon* symbol grammar (cons symbol seen))))
         (when (or res (null seen))
           (setf (grammar-derives-epsilon grammar)
                 (acons symbol res (grammar-derives-epsilon grammar))))
         res)))))

(defun derives-epsilon* (symbol grammar &optional seen)
  "Unmemoised version of DERIVES-EPSILON."
  (declare (symbol symbol) (type grammar grammar) (list seen))
  (dolist (production (grammar-productions grammar))
    (when (and (eq symbol (production-symbol production))
               (every #'(lambda (s) (derives-epsilon s grammar seen))
                      (production-derives production)))
      (return t))))

(defun sequence-derives-epsilon (sequence grammar)
  (declare (list sequence) (type grammar grammar))
  (every #'(lambda (s) (derives-epsilon s grammar)) sequence))

(defun derives-first (c grammar &optional seen)
  "The list of symbols A such that C rm->* A.eta for some eta."
  (declare (symbol c) (type grammar grammar) (list seen))
  (let ((e (assoc c (grammar-derives-first grammar))))
    (cond
      (e (the list (cdr e)))
      ((terminal-p c grammar) (list c))
      ((member c seen) '())
      (t
       (let ((derives (list c)))
         (declare (list derives))
         (dolist (production (grammar-productions grammar))
           (when (eq c (production-symbol production))
             (setq derives
                   (union (sequence-derives-first
                           (production-derives production) grammar
                           (cons c seen))
                          derives))))
         (when (null seen)
           (setf (grammar-derives-first grammar)
                 (acons c derives (grammar-derives-first grammar))))
         derives)))))

(defun sequence-derives-first (sequence grammar &optional seen)
  "Sequence version of DERIVES-FIRST."
  (declare (list sequence) (type grammar grammar) (list seen))
  (cond
    ((null sequence) '())
    ((terminal-p (car sequence) grammar) (list (car sequence)))
    (t
     (let ((d1 (derives-first (car sequence) grammar seen)))
       (if (derives-epsilon (car sequence) grammar)
           (union d1 (sequence-derives-first (cdr sequence) grammar seen))
           d1)))))

(defun derives-first-terminal (c grammar &optional seen)
  "The list of terminals a such that C rm->* a.eta, last non-epsilon."
  (declare (symbol c) (type grammar grammar))
  (let ((e (assoc c (grammar-derives-first-terminal grammar))))
    (cond
      (e (the list (cdr e)))
      ((terminal-p c grammar) (list c))
      ((member c seen) '())
      (t
       (let ((derives '()))
         (declare (list derives))
         (dolist (production (grammar-productions grammar))
           (when (eq c (production-symbol production))
             (setq derives
                   (union
                    (sequence-derives-first-terminal
                     (production-derives production) grammar (cons c seen))
                    derives))))
         (when (null seen)
           (push (cons c derives) (grammar-derives-first-terminal grammar)))
         derives)))))

(defun sequence-derives-first-terminal (sequence grammar &optional seen)
  (declare (list sequence) (type grammar grammar) (list seen))
  (cond
    ((null sequence) '())
    (t
     (derives-first-terminal (car sequence) grammar seen))))

(defun first-terminals (s grammar)
  "FIRST(s) without epsilon."
  (declare (atom s) (type grammar grammar))
  (cond
    ((terminal-p s grammar) (list s))
    (t (remove-if-not #'(lambda (s) (terminal-p s grammar))
                      (derives-first s grammar)))))

(defun sequence-first-terminals (s grammar)
  (declare (list s) (type grammar grammar))
  (cond
    ((null s) '())
    (t (let ((sf (first-terminals (car s) grammar)))
         (if (derives-epsilon (car s) grammar)
             (union sf (sequence-first-terminals (cdr s) grammar))
             sf)))))

(defun sequence-first (s grammar)
  "FIRST(s)."
  (declare (list s) (type grammar grammar))
  (let ((sf (sequence-first-terminals s grammar)))
    (if (sequence-derives-epsilon s grammar)
        (cons 'epsilon sf)
        sf)))

(defun combine-first (f1 s grammar)
  "FIRST(s1.s) where f1=FIRST(s1)."
  (declare (list f1 s) (type grammar grammar))
  (if (member 'epsilon f1)
      (union (remove 'epsilon f1) (sequence-first s grammar))
      f1))

(defun relative-first (s a grammar &optional seen)
  "Union of FIRST(eta) for all the eta s.t. S rm->* Aeta."
  (declare (symbol s a) (type grammar grammar) (list seen))
  (cond
    ((terminal-p s grammar) '())
    ((member s seen) '())
    (t (let ((res '()))
         (when (and (eq s a) (derives-epsilon s grammar))
           (push 'epsilon res))
         (dolist (p (grammar-productions grammar))
           (when (and (eq s (production-symbol p))
                      (not (null (production-derives p))))
             (setf res
                   (union res
                          (relative-first-sequence
                           (production-derives p)
                           a grammar (cons s seen))))))
         res))))

(defun relative-first-sequence (s a grammar &optional seen)
  (declare (list s seen) (symbol a) (type grammar grammar))
  (cond
    ((null s) '())
    ((equal s (list a)) (list 'epsilon))
    ((not (member (car s) (derives-first a grammar))) '())
    ((eq (car s) a) (sequence-first (cdr s) grammar))
    (t (relative-first (car s) a grammar seen))))

;;; Items

(defstruct (item
             (:constructor nil)
             (:print-function print-item)
             (:copier %copy-item))
  (production (required-argument) :type production)
  (position (required-argument) :type index))

(defstruct (lr0-item
             (:include item)
             (:constructor make-item (production position))
             (:conc-name item-))
  (lookaheads '() :type list))

(defstruct (lr1-item
             (:include item)
             (:constructor make-lr1-item
                           (production position lookahead))
             (:conc-name item-))
  (lookahead (required-argument) :type symbol))

(defun print-item (i s d)
  (declare (type item i) (stream s) (ignore d))
  (print-unreadable-object (i s :type t)
    (format s "~S -> ~{~S ~}. ~{~S~^ ~}"
            (item-symbol i) (item-dot-left i) (item-dot-right i))
    (when (lr1-item-p i)
      (format s " (~S)" (item-lookahead i)))))

(declaim (inline item-derives item-symbol item-action
                 item-dot-right-p item-dot-right item-dot-symbol
                 item-lr1-equal-p item-lr1-hash-value item-equal-p))

(defun item-derives (item)
  (declare (type item item))
  (production-derives (item-production item)))

(defun item-symbol (item)
  (declare (type item item))
  (production-symbol (item-production item)))

(defun item-action (item)
  (declare (type item item))
  (production-action (item-production item)))

(defun item-action-form (item)
  (declare (type item item))
  (production-action-form (item-production item)))

(defun item-lr1-equal-p (i1 i2)
  "Equality predicate for LR(1) items."
  (declare (type lr1-item i1 i2))
  (or (eq i1 i2)
      (and (eq (item-production i1) (item-production i2))
           (= (item-position i1) (item-position i2))
           (eq (item-lookahead i1) (item-lookahead i2)))))

(defun item-equal-p (i1 i2)
  "Compares items treating them as LR(0) items."
  (declare (type item i1 i2))
  (or (eq i1 i2)
      (and (eq (item-production i1) (item-production i2))
           (= (item-position i1) (item-position i2)))))

(defun item-lr1-hash-value (item)
  (declare (type lr1-item item))
  (cons (production-id (item-production item))
        (cons (item-position item)
              (item-lookahead item))))

(defun item< (i1 i2)
  (declare (type item i1 i2))
  (cond
    ((eq i1 i2) nil)
    ((production< (item-production i1) (item-production i2)) t)
    ((not (eq (item-production i1) (item-production i2))) nil)
    (t (< (item-position i1) (item-position i2)))))

(defun item-set-equal-p (c1 c2)
  "Equality predicate for sorted sets of LR(0) items."
  (declare (list c1 c2))
  (cond
    ((eq c1 c2) t)
    (t (do ((d1 c1 (cdr d1)) (d2 c2 (cdr d2)))
           ((or (eq d1 d2) (null d1) (null d2)) (eq d1 d2))
         (when (not (item-equal-p (car d1) (car d2)))
           (return nil))))))

(defun item-dot-right-p (item)
  (declare (type item item))
  (= (item-position item) (length (item-derives item))))

(defun item-dot-symbol (item)
  (declare (type item item))
  (nth (item-position item) (item-derives item)))

(defun item-dot-left (item)
  (subseq (item-derives item) 0 (item-position item)))

(defun item-dot-right (item &optional (n 0))
  (declare (type signed-index n))
  (nthcdr (+ n (item-position item)) (item-derives item)))

(defun item-shift (item &optional (n 1))
  (declare (type lr0-item item) (type signed-index n))
  (make-item (item-production item) (+ (item-position item) n)))

(defun lr1-item-shift (item &optional (n 1))
  (declare (type lr1-item item) (type signed-index n))
  (make-lr1-item (item-production item) (+ (item-position item) n)
                 (item-lookahead item)))


;;; Sets of items

(defstruct (kernel
             (:constructor %make-kernel (items))
             (:print-function print-kernel))
  (id nil :type (or null index))
  (items '() :type list)
  (gotos '() :type list))

(defun print-kernel (k s d)
  (declare (type kernel k) (stream s) (ignore d))
  (print-unreadable-object (k s :type t)
    (format s "~{~<~D ~:_~:>~}~_ ~D"
            (kernel-items k) (length (kernel-gotos k)))
    (when (kernel-id k)
      (format s " id=~D" (kernel-id k)))))

(defun make-kernel (items &optional kernels)
  (declare (list items kernels))
  (let* ((items (sort (copy-list items) #'item<))
         (k (find items kernels
                  :key #'kernel-items :test #'item-set-equal-p)))
    (or k (%make-kernel items))))

(defun kernel-item (kernel)
  (declare (type kernel kernel))
  (assert (null (cdr (kernel-items kernel))))
  (the lr0-item (car (kernel-items kernel))))

;; Items-closure starts by using a list, and switches to hashtables
;; later.  Using some sort of balanced tree would probably be better.

(defparameter *items-closure-hash-threshold* 20
  "The number of elements when items-closure switches to using a hashtable.")
(declaim (type (unsigned-byte 10) *items-closure-hash-threshold*))

(deftype lr1-collection () '(or list hash-table))

(defun make-lr1-collection (&optional same-kind-as)
  (etypecase same-kind-as
    (list '())
    (hash-table (make-hash-table :test #'equal))))

(defun lr1-collection-empty-p (collection)
  (declare (type lr1-collection collection))
  (typecase collection
    (list (null collection))
    (hash-table (zerop (hash-table-count collection)))))

(defun empty-lr1-collection (collection)
  (declare (type lr1-collection collection))
  (typecase collection
    (list '())
    (hash-table (clrhash collection))))

(defun make-hash-table-from-lr1-list (l)
  (declare (list l))
  (let ((h (make-hash-table :test #'equal)))
    (dolist (item l)
      (declare (type item item))
      (setf (gethash (item-lr1-hash-value item) h) item))
    h))

(declaim (inline lr1-find))
(defun lr1-find (item collection)
  (declare (optimize speed))
  (declare (type item item) (type lr1-collection collection))
  (typecase collection
    (list (find item collection :test #'item-lr1-equal-p))
    (hash-table (gethash (item-lr1-hash-value item) collection))))

(defun map-lr1-collection (f collection)
  (declare (dynamic-extent f))
  (declare (type lr1-collection collection))
  (typecase collection
    (list (mapcar f collection))
    (hash-table (maphash #'(lambda (k v) (declare (ignore k)) (funcall f v))
                         collection))))

(declaim (inline lr1-add))
(defun lr1-add (item collection)
  (declare (type lr1-item item) (type lr1-collection collection))
  (typecase collection
    (list (cons item collection))
    (hash-table
     (setf (gethash (item-lr1-hash-value item) collection) item)
     collection)))

(defun lr1-add-collection (items collection)
  (declare (type lr1-collection items collection))
  (typecase items
    (list
     (typecase collection
       (list (nconc items collection))
       (hash-table
        (dolist (item items)
          (setf (gethash (item-lr1-hash-value item) collection) item))
        collection)))
    (hash-table
     (typecase collection
       (list (error "This cannot happen"))
       (hash-table
        (maphash #'(lambda (k v) (setf (gethash k collection) v))
                 items)
        collection)))))

(defun items-closure (items grammar)
  "Compute the closure of a set of LR(1) items."
  (declare (list items) (type grammar grammar))
  (let ((res '()) (n 0)
        (threshold *items-closure-hash-threshold*))
    (declare (optimize speed))
    (declare (type (unsigned-byte 10) n) (type (or list hash-table) res))
    (labels ((add (item)
               (declare (type lr1-item item))
               (unless (lr1-find item res)
                 (setf res (lr1-add item res))
                 (when (listp res)
                   (incf n)
                   (when (> n threshold)
                     (setf res (make-hash-table-from-lr1-list res))))
                 (unless (item-dot-right-p item)
                   (let ((dot-symbol (item-dot-symbol item)))
                     (dolist (production (grammar-productions grammar))
                       (when (eq (production-symbol production) dot-symbol)
                         (dolist (terminal
                                   (sequence-first-terminals
                                    (append (item-dot-right item 1)
                                            (list (item-lookahead item)))
                                    grammar))
                           (add (make-lr1-item production 0 terminal))))))))))
      (mapc #'add items)
      res)))

;;; Goto transitions

(defstruct (goto
             (:constructor make-goto (symbol target)))
  (symbol nil :type symbol)
  (target (required-argument) :type kernel))

(declaim (inline goto-equal-p find-goto))
(defun goto-equal-p (g1 g2)
  (declare (type goto g1 g2))
  (and (eq (goto-symbol g1) (goto-symbol g2))
       ;; kernels are interned -- see make-kernel.
       (eq (goto-target g1) (goto-target g2))))

(defun find-goto (kernel symbol)
  (declare (type kernel kernel) (symbol symbol))
  (find symbol (kernel-gotos kernel) :key #'goto-symbol))

(defun compute-goto (kernel symbol grammar)
  "Compute the kernel of goto(KERNEL, SYMBOL)"
  (declare (type kernel kernel) (symbol symbol) (type grammar grammar))
  (let ((result '()))
    (dolist (item (kernel-items kernel))
      (when (not (item-dot-right-p item))
        (let ((c (item-dot-symbol item)))
          (when (eq c symbol)
            (pushnew (item-shift item) result :test #'item-equal-p))
          (dolist (production (grammar-productions grammar))
            (when (and (not (null (production-derives production)))
                       (eq symbol (car (production-derives production)))
                       (member (production-symbol production)
                               (derives-first c grammar)))
              (pushnew (make-item production 1) result
                       :test #'item-equal-p))))))
    result))

(defun compute-kernels (grammar)
  (declare (type grammar grammar))
  (let ((p0 (car (grammar-productions grammar))))
    (assert (= 1 (length (production-derives p0))))
    (let ((kernels '()))
      (declare (optimize speed))
      (labels
          ((add-goto (kernel symbol)
             (let* ((new-kernel*
                     (compute-goto kernel symbol grammar))
                    (new-kernel
                     (and new-kernel*
                          (make-kernel new-kernel* kernels)))
                    (new-goto (and new-kernel
                                   (make-goto symbol new-kernel))))
               (when new-kernel
                 (unless (member new-kernel kernels :test #'eq)
                   (add-kernel new-kernel))
                 (unless (member new-goto (kernel-gotos kernel)
                                 :test #'goto-equal-p)
                   (push new-goto (kernel-gotos kernel))))))
           (add-kernel (kernel)
             (push kernel kernels)
             (dolist (item (kernel-items kernel))
               (unless (item-dot-right-p item)
                 (add-goto kernel (item-dot-symbol item))))
             (dolist (production (grammar-productions grammar))
               (unless (null (production-derives production))
                 (add-goto kernel (car (production-derives production)))))))
        (add-kernel (make-kernel (list (make-item p0 0))))
        (nreverse kernels)))))

;;; Lookaheads

(defun compute-lookaheads (kernel grammar)
  (declare (type kernel kernel) (type grammar grammar))
  (let ((res '()))
    (declare (optimize speed))
    (declare (list res))
    (dolist (i (kernel-items kernel))
      (let ((j (items-closure
                (list
                 (make-lr1-item (item-production i) (item-position i)
                                'propagate))
                grammar)))
        (map-lr1-collection
         #'(lambda (item)
             (declare (type lr1-item item))
             (unless (item-dot-right-p item)
               (push (cons i (lr1-item-shift item)) res)))
         j)))
    res))

(defun compute-all-lookaheads (kernels grammar)
  (declare (list kernels) (type grammar grammar))
  (setf (item-lookaheads (kernel-item (car kernels))) (list 'eof))
  (let ((previously-changed kernels)
        (changed '()))
    (declare (optimize speed))
    (loop
     (dolist (kernel kernels)
       (when (member kernel previously-changed :test #'eq)
         (let ((lookaheads (compute-lookaheads kernel grammar)))
           (dolist (goto (kernel-gotos kernel))
             (declare (type goto goto))
             (let ((target (goto-target goto)) (new nil))
               (flet ((new-lookahead (item lookahead)
                        (declare (type lr1-item item) (symbol lookahead))
                        (let ((i (find item (kernel-items target)
                                       :test #'item-equal-p)))
                          (when i
                            (unless (member lookahead (item-lookaheads i))
                              (pushnew lookahead (item-lookaheads i))
                              (setq new t))))))
                 (dolist (e lookaheads)
                   (let ((i (car e)) (ni (cdr e)))
                     (declare (type lr0-item i) (type lr1-item ni))
                     (cond
                       ((eq 'propagate (item-lookahead ni))
                        ;; propagate
                        (let ((item (find i (kernel-items kernel)
                                          :test #'item-equal-p)))
                          (when item
                            (dolist (s (item-lookaheads item))
                              (new-lookahead ni s)))))
                       (t
                        ;; spontaneous generation
                        (new-lookahead ni (item-lookahead ni)))))))
               (when new
                 (pushnew target changed)))))))
     (unless changed (return))
     (psetq previously-changed changed
            changed '())))
  kernels)

(defun print-states (kernels lookaheads &optional (stream *standard-output*))
  (declare (list kernels))
  (let ((stream (etypecase stream
             ((member nil) *standard-output*)
             ((member t) *terminal-io*)
             (stream stream))))
    (declare (stream stream) #+CMU (optimize ext:inhibit-warnings))
    (pprint-logical-block (stream kernels)
      (loop
       (pprint-exit-if-list-exhausted)
       (let ((k (pprint-pop)))
         (format stream "~S: " (kernel-id k))
         (pprint-logical-block (stream (kernel-items k))
           (loop
            (pprint-exit-if-list-exhausted)
            (let* ((item (pprint-pop)))
              (if lookaheads
                  (format stream "~S ~_~S~:@_" item (item-lookaheads item))
                  (format stream "~S~:@_" item)))))
         (format stream "~_"))))))

;;; Parser generation

(defun number-kernels (kernels)
  "Set ID for all kernels in KERNELS."
  (declare (list kernels))
  (let ((id 0))
    (dolist (k kernels)
      (setf (kernel-id k) id)
      (incf id))))

(defun print-goto-graph (kernels &optional (stream *standard-output*))
  "Print the goto graph defined by KERNELS."
  (declare (list kernels))
  (let ((stream (etypecase stream
             ((member nil) *standard-output*)
             ((member t) *terminal-io*)
             (stream stream))))
    (declare (stream stream) #+CMU (optimize ext:inhibit-warnings))
    (pprint-logical-block (stream kernels)
      (loop
       (pprint-exit-if-list-exhausted)
       (let ((k (pprint-pop)))
         (format stream "~S: " (kernel-id k))
         (pprint-logical-block (stream (kernel-gotos k))
           (loop
            (pprint-exit-if-list-exhausted)
            (let ((g (pprint-pop)))
              (format stream "~S -> ~S ~@:_"
                      (goto-symbol g) (kernel-id (goto-target g))))))
         (format stream "~@:_"))))))

(defstruct (action (:constructor nil)
                   (:print-function print-action))
  )

(defstruct (accept-action (:include action))
  )

(defstruct (reduce-action (:include action)
                          (:constructor make-reduce-action
                                        (symbol length
                                         &key action action-form)))
  (symbol (required-argument) :type symbol)
  (length (required-argument) :type index)
  (action #'list :type function)
  (action-form nil))

(defstruct (shift-action (:include action)
                         (:constructor
                          make-shift-action (state)))
  (state (required-argument) :type index))

(defstruct (error-action (:include action))
  )

(defun action-equal-p (a1 a2)
  (declare (type action a1 a2))
  (or (eq a1 a2)
      (and
       (eq (type-of a1) (type-of a2))
       (typecase a1
         (reduce-action
          (and (eq (reduce-action-symbol a1) (reduce-action-symbol a2))
               (= (reduce-action-length a1) (reduce-action-length a2))
               (eq (reduce-action-action a1) (reduce-action-action a2))))
         (shift-action
          (= (shift-action-state a1) (shift-action-state a2)))
         (t t)))))

(defun print-action (a s d)
  (declare (type action a) (stream s) (ignore d))
  (print-unreadable-object (a s :type t)
    (typecase a
      (reduce-action
       (format s "~S (~D)" (reduce-action-symbol a) (reduce-action-length a)))
      (shift-action
       (format s "~D" (shift-action-state a))))))

(define-condition conflict-warning (simple-warning)
  ((kind :initarg :kind :reader conflict-warning-kind)
   (state :initarg :state :reader conflict-warning-state)
   (terminal :initarg :terminal :reader conflict-warning-terminal))
  (:report (lambda (w stream)
             (format stream "~A conflict on terminal ~S in state ~A, ~
                             ~_~?"
                     (case (conflict-warning-kind w)
                       (:shift-reduce "Shift/Reduce")
                       (:reduce-reduce "Reduce/Reduce")
                       (t (conflict-warning-kind w)))
                     (conflict-warning-terminal w)
                     (conflict-warning-state w)
                     (simple-condition-format-control w)
                     (simple-condition-format-arguments w)))))

(define-condition conflict-summary-warning (warning)
  ((shift-reduce :initarg :shift-reduce
                 :reader conflict-summary-warning-shift-reduce)
   (reduce-reduce :initarg :reduce-reduce
                  :reader conflict-summary-warning-reduce-reduce))
  (:report (lambda (w stream)
             (format stream "~D Shift/Reduce, ~D Reduce/Reduce conflicts"
                     (conflict-summary-warning-shift-reduce w)
                     (conflict-summary-warning-reduce-reduce w)))))

(defstruct (parser (:constructor %make-parser (states goto action)))
  (states (required-argument) :type index)
  (goto (required-argument) :type simple-vector)
  (action (required-argument) :type simple-vector))

(defun handle-conflict (a1 a2 i s &optional item)
  (declare (type action a1 a2) (type index i) (symbol s))
  (when (action-equal-p a1 a2)
    (return-from handle-conflict (values a1 0 0)))
  (when (and (shift-action-p a2) (reduce-action-p a1))
    (psetq a1 a2 a2 a1))
  (warn (make-condition
         'conflict-warning
         :kind (typecase a1
                 (shift-action :shift-reduce)
                 (t :reduce-reduce))
         :state i :terminal s
         :format-control "~S and ~S~@[ ~_~A~]"
         :format-arguments (list a1 a2 item)))
  (typecase a1
    (shift-action (values a1 1 0))
    (t (values a1 0 1))))

(defun compute-parsing-tables (kernels grammar)
  (declare (list kernels) (type grammar grammar))
  (let ((numkernels (length kernels)))
    (let ((goto (make-array numkernels :initial-element '()))
          (action (make-array numkernels :initial-element '()))
          (sr-conflicts 0) (rr-conflicts 0)
          (epsilon-productions (grammar-epsilon-productions grammar)))
      (flet ((set-action (k symbols a &optional item)
               (let ((i (kernel-id k)))
                 (dolist (s symbols)
                   (if (assoc s (aref action i))
                       (multiple-value-bind (new-action s-r r-r)
                           (handle-conflict
                            (cdr (assoc s (aref action i)))
                            a i s item)
                         (setf (cdr (assoc s (aref action i))) new-action)
                         (incf sr-conflicts s-r) (incf rr-conflicts r-r))
                       (push (cons s a) (aref action i))))))
             (set-goto (k symbols target)
               (let ((i (kernel-id k)) (j (kernel-id target)))
                 (dolist (s symbols)
                   (let ((e (assoc s (aref goto i))))
                     (when e
                       (assert (eq j (cdr e)))
                       (return-from set-goto)))
                   (push (cons s j) (aref goto i))))))
        (do* ((ks kernels (cdr ks)) (k (car ks) (car ks)))
             ((null ks))
          (dolist (item (kernel-items k))
            (cond
              ((item-dot-right-p item)
               ;; non-epsilon reduction
               (let ((la (item-lookaheads item)))
                 (cond
                   ((and (eq 's-prime (item-symbol item))
                         (= 1 (item-position item)))
                    (when (member 'eof la)
                      (set-action k (list 'eof)
                                  (make-accept-action))))
                   (t
                    (set-action k la
                                (make-reduce-action
                                 (item-symbol item)
                                 (length (item-derives item))
                                 :action (item-action item)
                                 :action-form (item-action-form item))
                                item)))))
              (t
               (let ((c (item-dot-symbol item)))
                 ;; shift
                 (let ((a (derives-first-terminal c grammar)))
                   (dolist (s a)
                     (let ((g (find-goto k s)))
                       (when g
                         (set-action k (list s)
                                     (make-shift-action
                                      (kernel-id (goto-target g)))
                                     item)))))
                 ;; epsilon reduction
                 (dolist (a-epsilon epsilon-productions)
                   (let ((a (production-symbol a-epsilon)))
                     (when (member a (derives-first c grammar))
                       (let* ((first-eta
                               (relative-first c a grammar))
                              (first-eta-delta
                               (combine-first first-eta
                                              (item-dot-right item 1) grammar))
                              (first-eta-delta-b
                               (if (member 'epsilon first-eta-delta)
                                   (union (remove 'epsilon first-eta-delta)
                                          (item-lookaheads item))
                                   first-eta-delta)))
                         (set-action
                          k first-eta-delta-b
                          (make-reduce-action
                           a 0
                           :action (production-action a-epsilon)
                           :action-form (production-action-form a-epsilon)))
                         ))))
                 ))))
          (dolist (g (kernel-gotos k))
            (when (not (terminal-p (goto-symbol g) grammar))
              (set-goto k (list (goto-symbol g)) (goto-target g))))))
      (when (not (zerop (+ sr-conflicts rr-conflicts)))
        (warn (make-condition 'conflict-summary-warning
                              :shift-reduce sr-conflicts
                              :reduce-reduce rr-conflicts)))
      (%make-parser numkernels goto action))))

(defun make-parser (grammar
                    &key (discard-memos t) (print-states nil)
                    (print-goto-graph nil) (print-lookaheads nil))

  (declare (type grammar grammar))
  (let ((kernels (compute-kernels grammar)))
    (compute-all-lookaheads kernels grammar)
    (number-kernels kernels)
    (when print-goto-graph (print-goto-graph kernels))
    (when (or print-states print-lookaheads)
      (print-states kernels print-lookaheads))
    (prog1
        (compute-parsing-tables kernels grammar)
      (when discard-memos (grammar-discard-memos grammar)))))

(define-condition yacc-parse-error (error)
  ((terminal :initarg :terminal :reader yacc-parse-error-terminal)
   (value :initarg :value :reader yacc-parse-error-value)
   (expected-terminals :initarg :expected-terminals
                       :reader yacc-parse-error-expected-terminals))
  (:report (lambda (e stream)
             (format stream "Unexpected terminal ~S (value ~S)~@:_~
                             Expected one of: ~S"
                     (yacc-parse-error-terminal e)
                     (yacc-parse-error-value e)
                     (yacc-parse-error-expected-terminals e)))))

(defun parse-with-lexer (lexer parser)
  (declare (type (function () (values symbol t)) lexer))
  (declare (type parser parser))
  (let ((action-array (parser-action parser))
        (goto-array (parser-goto parser)))
    (flet ((action (i a)
             (declare (type index i) (symbol a))
             (or (cdr (assoc a (aref action-array i)))
                 (make-error-action)))
           (goto (i a)
             (declare (type index i) (symbol a))
             (or (cdr (assoc a (aref goto-array i)))
                 (error "This cannot happen."))))
      (let ((stack (list 0)) symbol value)
        (flet ((next-symbol ()
                 (multiple-value-bind (s v) (funcall lexer)
                   (setq symbol (or s 'eof) value v))))
          (next-symbol)
          (loop
           (let* ((state (car stack))
                  (action (action state symbol)))
             (etypecase action
               (shift-action
                (push value stack)
                (push (shift-action-state action) stack)
                (next-symbol))
               (reduce-action
                (let ((vals '()))
                  (dotimes (n (reduce-action-length action))
                    (pop stack)
                    (push (pop stack) vals))
                  (let ((s* (car stack)))
                    (push (apply (reduce-action-action action) vals) stack)
                    (push (goto s* (reduce-action-symbol action)) stack))))
               (accept-action
                (pop stack)
                (return (pop stack)))
               (error-action
                (error (make-condition
                        'yacc-parse-error
                        :terminal symbol :value value
                        :expected-terminals
                        (mapcar #'car (aref action-array state)))))
               ))))))))

;;; User interface

(defun parse-production (form)
  (let ((symbol (car form))
        (productions '()))
    (dolist (stuff (cdr form))
      (cond
        ((and (symbolp stuff) (not (null stuff)))
         (push (make-production symbol (list stuff)
                                :action #'identity :action-form '#'identity)
               productions))
        ((listp stuff)
         (let ((l (car (last stuff))))
           (let ((rhs (if (symbolp l) stuff (butlast stuff)))
                 (action (if (symbolp l) '#'list l)))
             (push (make-production symbol rhs
                     :action (eval action)
                     :action-form action)
                   productions))))
        (t (error "Unexpected production ~S" stuff))))
    productions))

(defun parse-grammar (forms)
  (let ((options '()) (make-options '()) (productions '()))
    (dolist (form forms)
      (cond
        ((member (car form)
                 '(:print-states :print-goto-graph :print-lookaheads))
         (unless (null (cddr form))
           (error "Malformed option ~S" form))
         (push (car form) make-options)
         (push (cadr form) make-options))
        ((keywordp (car form))
         (unless (null (cddr form))
           (error "Malformed option ~S" form))
         (push (car form) options)
         (push (cadr form) options))
        ((symbolp (car form))
         (setq productions (nconc (parse-production form) productions)))
        (t
         (error "Unexpected grammar production ~S" form))))
    (values (nreverse options) (nreverse make-options)
            (nreverse productions))))

(defparameter *max-list-elements* (min call-arguments-limit 1024)
  "The actual list size used by DUMP-LIST.")

(defun dump-list (list)
  "Like `(LIST ,@LIST), but avoids CALL-ARGUMENTS-LIMIT."
  (declare (type list list))
  (if (<= (length list) *max-list-elements*)
      `(list ,@list)
      (do ((lists '())
           (list list (nthcdr *max-list-elements* list)))
          ((null list) `(reduce #'append (list ,@(nreverse lists))))
        (push `(list ,@(subseq list 0 (min (length list) *max-list-elements*)))
              lists))))

(defmacro define-grammar (name &body body)
  (multiple-value-bind (options make-options productions) (parse-grammar body)
    (declare (ignore make-options))
    `(defparameter ,name
      ',(apply #'make-grammar
               :name name
               :productions productions
               options))))

(defmacro define-parser (name &body body)
  (multiple-value-bind (options make-options productions) (parse-grammar body)
    `(defparameter ,name
      ',(apply #'make-parser
               (apply #'make-grammar
                      :name name
                      :productions productions
                      options)
               make-options))))

;;; Support for fasdumping grammars and parsers.

(defmethod make-load-form ((p production) &optional env)
  (declare (ignore env))
  (when (null (production-action-form p))
    (error "Production ~S cannot be dumped (it has no action form)" p))
  (values
   `(make-production ',(production-symbol p) ',(production-derives p))
   `(setf (production-action-form ,p) ',(production-action-form p)
          (production-action ,p) (eval ',(production-action-form p)))))

(defmethod make-load-form ((g grammar) &optional env)
  (make-load-form-saving-slots g :environment env))

(defmethod make-load-form ((p parser) &optional env)
  (make-load-form-saving-slots p :environment env))

(defmethod make-load-form ((a accept-action) &optional env)
  (declare (ignore env))
  `(make-accept-action))

(defmethod make-load-form ((a reduce-action) &optional env)
  (declare (ignore env))
  (when (null (reduce-action-action-form a))
    (error "Action ~S cannot be dumped (it has no action form)" a))
  (values
   `(make-reduce-action ',(reduce-action-symbol a) ',(reduce-action-length a))
   `(setf (reduce-action-action-form ,a) ',(reduce-action-action-form a)
          (reduce-action-action ,a) (eval ',(reduce-action-action-form a)))))

(defmethod make-load-form ((a shift-action) &optional env)
  (declare (ignore env))
  `(make-shift-action ',(shift-action-state a)))
