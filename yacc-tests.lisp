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

(defpackage #:yacc-tests
  (:export tests)
  (:use #:cl #:yacc))

(in-package #:yacc-tests)

(defmacro expect-condition (class &body body)
  (let ((name (gensym "EXPECT-CONDITION")))
  `(block ,name
    (handler-case (progn ,@body)
      (,class () (return-from ,name nil)))
    (error "~S didn't signal a ~S" ',body ',class))))

;;; A trivial lexer

(defun list-lexer (list)
  #'(lambda ()
      (let ((x (pop list)))
        (values x x))))

;;; A few grammars from the Dragon book

(defun make-grammar-4-31 ()
  (make-grammar :terminals '(+ * id lb rb)
                :start-symbol 'e
                :productions
                (list (make-production 'e '(e + tt))
                      (make-production 'e '(tt) :action #'identity)
                      (make-production 'tt '(tt * f))
                      (make-production 'tt '(f) :action #'identity)
                      (make-production 'f '(lb e rb))
                      (make-production 'f '(id) :action #'identity))))

;; This grammar is LALR(1) but not SLR

(defun make-grammar-4-20 ()
  (make-grammar :terminals '(id * =)
                :start-symbol 's
                :productions
                (list (make-production 's '(l = r))
                      (make-production 's '(r))
                      (make-production 'l '(* r))
                      (make-production 'l '(id))
                      (make-production 'r '(l)))))

(defun make-grammar-4-21 ()
  (make-grammar :terminals '(c d)
                :start-symbol 's
                :productions
                (list (make-production 's '(cc cc))
                      (make-production 'cc '(c cc))
                      (make-production 'cc '(d)))))

;;; Epsilon-reductions on the left and right side

(defun make-grammar-epsilon-left ()
  (make-grammar :terminals '(id)
                :start-symbol 's
                :productions
                (list (make-production 's '())
                      (make-production 's '(s id)))))

(defun make-grammar-epsilon-right ()
  (make-grammar :terminals '(id)
                :start-symbol 's
                :productions
                (list (make-production 's '())
                      (make-production 's '(id s)))))

(defun tests-low ()
  (let ((parser-4-31 (make-parser (make-grammar-4-31)))
        (parser-4-20 (make-parser (make-grammar-4-20)))
        (parser-4-21 (make-parser (make-grammar-4-21)))
        (parser-epsilon-left (make-parser (make-grammar-epsilon-left)))
        (parser-epsilon-right (make-parser (make-grammar-epsilon-right))))
    (flet ((accepts (parser list &optional (result nil result-p))
             (let ((p (parse-with-lexer (list-lexer list) parser)))
               (when result-p
                 (assert (equal p result))))))
      (accepts parser-4-31 '(lb id + id * id rb) '(LB (ID + (ID * ID)) RB))
      (accepts parser-4-31 '(lb id * id + id rb) '(lb ((id * id) + id) rb))
      (accepts parser-4-20 '(* id = * * id) '((* ((id))) = ((* ((* ((id))))))))
      (accepts parser-4-21 '(c d c d) '((c (d)) (c (d))))
      (accepts parser-epsilon-left '())
      (accepts parser-epsilon-left '(id))
      (accepts parser-epsilon-left '(id id))
      (accepts parser-epsilon-right '())
      (accepts parser-epsilon-right '(id))
      (accepts parser-epsilon-right '(id id))
      nil)))

;;; Some higher-level tests

(defun digitp (c) (member c '(#\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9 #\0)))

(defun simple-lexer (stream)
  (let ((c (read-char stream nil nil)))
    (cond
      ((null c) (values nil nil))
      ((eql c #\Newline) (values nil nil))
      ((member c '(#\Space #\Tab)) (simple-lexer stream))
      ((member c '(#\+ #\- #\* #\/ #\( #\)))
       (let ((v (intern (string c))))
         (values v v)))
      ((digitp c)
       (let ((buffer (make-array 10 :element-type 'character
                                 :fill-pointer 0)))
         (do ((c c (read-char stream nil nil)))
             ((or (null c) (not (digitp c)))
              (unless (null c) (unread-char c stream))
              (values 'int (read-from-string buffer)))
           (vector-push-extend c buffer))))
      ((alpha-char-p c)
       (let ((buffer (make-array 10 :element-type 'character
                                 :fill-pointer 0)))
         (do ((c c (read-char stream nil nil)))
             ((or (null c) (not (alphanumericp c)))
              (unless (null c) (unread-char c stream))
              (values 'id (copy-seq buffer)))
           (vector-push-extend c buffer))))
      (t (error "Lexing error")))))

(eval-when (compile load eval)
  (defun k-2-3 (a b c) (declare (ignore a c)) b)
)

(define-parser *left-expression-parser*
  (:start-symbol expression)
  (:terminals (int id + - * / |(| |)|))

  (expression
   (expression + term)
   (expression - term)
   term)

  (term
   (term * factor)
   (term / factor)
   factor)

  (factor
   id
   int
   (|(| expression |)| #'k-2-3)))

(defun parse-left-expression (stream)
  (parse-with-lexer #'(lambda () (simple-lexer stream))
                    *left-expression-parser*))

(defun tests-hi ()
  (let ((*package* (find-package '#:yacc-tests)))
    (with-input-from-string (s "5/3*(12+foo)/3+foo")
      (parse-left-expression s))
    (expect-condition yacc-parse-error
      (with-input-from-string (s "5/3*(")
        (parse-left-expression s)))
    (expect-condition yacc-parse-error
      (with-input-from-string (s "5/3)")
        (parse-left-expression s)))
    nil))

(defun tests ()
  (tests-low)
  (tests-hi)
  nil)

