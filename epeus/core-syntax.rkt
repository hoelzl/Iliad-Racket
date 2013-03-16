;;; Syntax used in the implementation of the core of Epeus.

;;; Written by Matthias Hölzl (tc@xantira.com)

;;; This file contains the syntax definitions that are used in the
;;; core of the Epeus implementation.  Some of these forms will be
;;; exported, but most of them are for the internal use of the object
;;; system.  The complex user-visible macros can be found in the file
;;; `syntax.rkt'.

#lang racket

(require "utils.rkt")
(require (for-syntax racket))
(require (for-syntax racket/syntax))
(require (for-syntax syntax/parse))


;;;; Debugging and Bootstrapping Support
;;;; -----------------------------------

;;; For debugging
;;; (require macro-debugger/stepper)

;;; TODO: For bootstrapping purposes only - remove once the system is actually
;;; running.
(provide define-placeholder)
(define-syntax-rule (define-placeholder name)
  (define name 'placeholder))

;;; TODO: For bootstrapping purposes only - remove once the system is actually
;;; running.
(provide define-placeholders)
(define-syntax-rule (define-placeholders name ...)
  (begin
    (define-placeholder name) ...))


;;;; Support for tests
;;;; -----------------

(provide provide-test-export)
(define-syntax-rule (provide-test-export id0 id ...)
  (module+ test-exports (provide id0 id ...)))



;;;; Definition Definitions
;;;; ----------------------

(provide define/macro)
(define-syntax (define/macro stx)
  (syntax-case stx ()
    [(_ (name args ...) body ...)
     (identifier? #'name)
     (with-syntax ([macro-name (datum->syntax #'name
                                              (format-symbol "%~a" #'name)
                                              #'name)])
       #'(begin
           (define (name args ...)
             body ...)
           (define-syntax-rule (macro-name args ...)
             body ...)))]))


;;;; Keyword Procedures
;;;; ------------------

(provide make-keyword-procedure-0)
(define-syntax-rule (make-keyword-procedure-0 proc)
  (procedure-reduce-keyword-arity
   (make-keyword-procedure proc)
   (arity-at-least 0)
   '()
   #f))

(provide make-keyword-procedure-1)
(define-syntax-rule (make-keyword-procedure-1 proc)
  (procedure-reduce-keyword-arity
   (make-keyword-procedure proc)
   (arity-at-least 1)
   '()
   #f))

(provide make-keyword-procedure-n)
(define-syntax-rule (make-keyword-procedure-n n proc)
  (procedure-reduce-keyword-arity
   (make-keyword-procedure proc)
   (arity-at-least n)
   '()
   #f))

(provide kw-lambda)
(define-syntax (kw-lambda stx)
  (syntax-case stx ()
    [(_ (kws kw-args pos-arg ...) body ...)
     #`(procedure-reduce-keyword-arity
        (make-keyword-procedure
         (lambda (kws kw-args pos-arg ...)
           body ...))
        #,(length (syntax-e #'(pos-arg ...)))
        '()
        #f)]
    [(_ (kws kw-args pos-arg ... . rest-arg) body ...)
     #`(procedure-reduce-keyword-arity
        (make-keyword-procedure
         (lambda (kws kw-args pos-arg ... . rest-arg)
           body ...))
        (arity-at-least #,(length (syntax-e #'(pos-arg ...))))
        '()
        #f)]))


;;;; Generics
;;;; --------

(provide generic->property-descriptor)
(define-syntax (generic->property-descriptor stx)
  (syntax-case stx ()
    [(_ id) (car (syntax-local-value #'id))]))
