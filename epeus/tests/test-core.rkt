#lang racket

;;; Tests for the tiny-clos module.

(require "../core.rkt")
(require (submod "../core.rkt" test-exports))
(require rackunit)
(require rackunit/text-ui)

(provide epeus-core-suite)

(define-test-suite epeus-core-suite
  (test-case
   "merge-sorted-keyword-lists 1"
   (let-values ([(keys vals)
		 (merge-sorted-keyword-lists '(#:a #:c) '(a1 c1)
					     '(#:b #:d) '(b2 d2))])
     (check-equal? keys '(#:a #:b #:c #:d))
     (check-equal? vals '(a1 b2 c1 d2))))

  (test-case
   "merge-sorted-keyword-lists 2"
   (let-values ([(keys vals)
		 (merge-sorted-keyword-lists '(#:b #:d #:e) '(b1 d1 e1)
					     '(#:a #:c) '(a2 c2))])
     (check-equal? keys '(#:a #:b #:c #:d #:e))
     (check-equal? vals '(a2 b1 c2 d1 e1))))

  (test-case
   "merge-sorted-keyword-lists 3"
   (let-values ([(keys vals)
		 (merge-sorted-keyword-lists '(#:a #:c #:x)     '(a1 c1 x1)
					     '(#:b #:c #:d #:e) '(b2 c2 d2 e2))])
     (check-equal? keys '(#:a #:b #:c #:c #:d #:e #:x))
     (check-equal? vals '(a1 b2 c1 c2 d2 e2 x1))))

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

  ;;; TODO: Add tests for `top-sort' and helpers


)
