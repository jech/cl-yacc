;;; -*-Lisp-*-

(asdf:defsystem #:yacc
  :name "yacc"
  :author "Juliusz Chroboczek <jch@irif.fr>"
  :licence "MIT/X11"
  :description "A LALR(1) parser generator for Common Lisp"
  :components ((:file "yacc"))
  )
