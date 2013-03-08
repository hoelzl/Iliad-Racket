#lang racket

;;; Tests for the tiny-clos module.

(require "../tiny-clos.rkt")
(require (submod "../tiny-clos.rkt" test-exports))
(require rackunit)
(require rackunit/text-ui)

(provide tiny-clos-suite)

(define-test-suite tiny-clos-suite

  (test-case
   "raise* 1"
   (check-exn exn:fail?
	      (thunk
	       (raise* make-exn:fail "fail ~a, ~a, ~a" 1 2 3)))
   (check-exn #rx"^fail 1, 2, 3$"
	      (thunk
	       (raise* make-exn:fail "fail ~a, ~a, ~a" 1 2 3))
	      "Wrong exception message"))

  (test-case
   "raise* 2"
   (check-exn exn:fail?
	      (thunk
	       (raise* #:context-name 'one-two-three
		       make-exn:fail "fail ~a, ~a, ~a" 1 2 3)))
   (check-exn #rx"^one-two-three: fail 1, 2, 3$"
	      (thunk
	       (raise* #:context-name 'one-two-three
		       make-exn:fail "fail ~a, ~a, ~a" 1 2 3))
	      "Wrong exception message"))

  (test-case
   "raise* 3"
   (check-exn exn:fail:contract:variable?
	      (thunk
	       (raise* make-exn:fail:contract:variable
		       "fail ~a, ~a, ~a" 1 2 3
		       'my-var)))
   (check-exn #rx"^fail-var 1, 2, 3$"
	      (thunk
	       (raise* make-exn:fail:contract:variable
		       "fail-var ~a, ~a, ~a" 1 2 3
		       'my-var))
	      "Wrong exception message")
   (check-exn (lambda (exn)
		(check-eq? 'my-var (exn:fail:contract:variable-id exn)))
	      (thunk
	       (raise* make-exn:fail:contract:variable
		       "fail-var ~a, ~a, ~a" 1 2 3
		       'my-var))
	      "Wrong exception message"))

  (test-case
   "raise* 4"
   (check-exn exn:fail:contract:variable?
	      (thunk
	       (raise* #:context-name 'one-two-three
		       make-exn:fail:contract:variable
		       "fail ~a, ~a, ~a" 1 2 3
		       'my-var)))
   (check-exn #rx"^one-two-three: fail-var 1, 2, 3$"
	      (thunk
	       (raise* #:context-name 'one-two-three
		       make-exn:fail:contract:variable
		       "fail-var ~a, ~a, ~a" 1 2 3
		       'my-var))
	      "Wrong exception message")
   (check-exn (lambda (exn)
		(check-eq? 'my-var (exn:fail:contract:variable-id exn)))
	      (thunk
	       (raise* #:context-name 'one-two-three
		       make-exn:fail:contract:variable
		       "fail-var ~a, ~a, ~a" 1 2 3
		       'my-var))
	      "Wrong exception message"))
)
