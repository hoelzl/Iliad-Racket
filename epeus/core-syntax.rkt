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
(define-syntax (define-placeholder stx)
  (syntax-parse stx
    [(_ name:id)
     #'(define name 'placeholder)]))

;;; TODO: For bootstrapping purposes only - remove once the system is actually
;;; running.
(provide define-placeholders)
(define-syntax (define-placeholders stx)
  (syntax-parse stx
    [(_ name:id ...)
     #'(begin
         (define-placeholder name) ...)]))


;;;; Support for tests
;;;; -----------------

(provide provide-test-export)
(define-syntax (provide-test-export stx)
  (syntax-parse stx
    [(_ name:id ...+)
     #'(module+ test-exports (provide name ...))]))


;;;; Definition Definitions
;;;; ----------------------

(provide define/macro)
(define-syntax (define/macro stx)
  (syntax-parse stx
    [(_ (name:id arg:id ...) body:expr ...)
     (with-syntax ([macro-name (datum->syntax #'name
                                              (format-symbol "%~a" #'name)
                                              #'name)])
       #'(begin
           (define (name arg ...)
             body ...)
           (define-syntax-rule (macro-name arg ...)
             body ...)))]))


;;;; Keyword Procedures
;;;; ------------------

(provide make-keyword-procedure-at-least-n)
(define-syntax-rule (make-keyword-procedure-at-least-n stx)
  (syntax-parse stx
    [(_ n:nat proc:expr)
     (procedure-reduce-keyword-arity
      (make-keyword-procedure proc)
      (arity-at-least n)
      '()
      #f)]))

(provide (for-syntax arg opt-arg))
(begin-for-syntax

  (define-syntax-class arg
    (pattern id:id)
    (pattern [id:id default:expr]))

  (define-syntax-class opt-arg
    (pattern [id:id default:expr])))

(define-for-syntax (arity-between m n)
  (if (m . > . n)
      null
      (list* m (arity-between (add1 m) n))))

(provide kw-lambda)
(define-syntax (kw-lambda stx)
  (syntax-parse stx
    [(_ (kws:id kw-args:id 
         req-arg:id ... opt-arg:opt-arg ...)
        body:expr ...+)
     #`(procedure-reduce-keyword-arity
        (make-keyword-procedure
         (lambda (kws kw-args req-arg ... opt-arg ...)
           body ...))
        '#,(let ([req-args (syntax-e #'(req-arg ...))]
                 [opt-args (syntax-e #'(opt-arg ...))])
             (if (null? opt-args)
                 (length req-args)
                 (arity-between (length req-args)
                                (+ (length req-args) (length opt-args)))))
        null
        #f)]
    [(_ (kws:id kw-args:id 
         req-arg:id ... opt-arg:opt-arg ... . rest-arg:id)
        body:expr ...+)
     #`(procedure-reduce-keyword-arity
        (make-keyword-procedure
         (lambda (kws kw-args req-arg ... opt-arg ... . rest-arg)
           body ...))
        (arity-at-least #,(length (syntax-e #'(req-arg ...))))
        null
        #f)]))


;;;; Generics
;;;; --------

(provide generic->property-descriptor)
(define-syntax (generic->property-descriptor stx)
  (syntax-parse stx
    [(_ id:id) (first (syntax-local-value #'id))]))
