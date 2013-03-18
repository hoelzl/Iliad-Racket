#lang racket

;;; Test for the utilities module.

(require racket/block)
(require "../utils.rkt")
;; (require (submod "../utils.rkt" test-exports))
(require rackunit)
(require rackunit/text-ui)

(provide epeus-utils-suite)

(define-test-suite epeus-utils-suite
  (test-case "position-of"
    (check-equal? (position-of 'a '()) #f)
    (check-equal? (position-of 'a '(a b c)) 0)
    (check-equal? (position-of 'b '(a b c)) 1)
    (check-equal? (position-of 'c '(a b c)) 2)
    (check-equal? (position-of 'd '(a b c)) #f))

  (test-case "raise* 1"
    (check-exn exn:fail?
               (thunk
                (raise* make-exn:fail "fail ~a, ~a, ~a" 1 2 3)))
    (check-exn #rx"^fail 1, 2, 3$"
               (thunk
                (raise* make-exn:fail "fail ~a, ~a, ~a" 1 2 3))
               "Wrong exception message"))

  (test-case "raise* 2"
    (check-exn exn:fail?
               (thunk
                (raise* #:context-name 'one-two-three
                        make-exn:fail "fail ~a, ~a, ~a" 1 2 3)))
    (check-exn #rx"^one-two-three: fail 1, 2, 3$"
               (thunk
                (raise* #:context-name 'one-two-three
                        make-exn:fail "fail ~a, ~a, ~a" 1 2 3))
               "Wrong exception message"))
  
  (test-case "raise* 3"
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
  
  (test-case "raise* 4"
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
  
  (test-case "keyword->symbol"
    (define key-sym (keyword->symbol '#:my-keyword))
    (check-pred symbol? key-sym)
    (check-equal? key-sym 'my-keyword))

  (block
   (define no-kw   (lambda (x) x))
   (define no-kw*  (lambda x x))
   (define req-kw  (lambda (#:key key x) (list key x)))
   (define req-kw* (lambda (#:key key . x) (list key x)))
   (define opt-kw  (lambda (#:key [key #t] x) (list key x)))
   (define opt-kw* (lambda (#:key [key #t] x) (list key x)))
   (define all-kw  (make-keyword-procedure
                    (lambda (kws kw-args x) (list kws kw-args x))))
   (define all-kw*  (make-keyword-procedure
                     (lambda (kws kw-args . x) (list kws kw-args x))))

   (test-case "procedure-accepts-keywords?"
     (check-false (procedure-accepts-keywords? no-kw))
     (check-false (procedure-accepts-keywords? no-kw*))
     (check-true (procedure-accepts-keywords? req-kw))
     (check-true (procedure-accepts-keywords? req-kw*))
     (check-true (procedure-accepts-keywords? opt-kw))
     (check-true (procedure-accepts-keywords? opt-kw*))
     (check-true (procedure-accepts-keywords? all-kw))
     (check-true (procedure-accepts-keywords? all-kw*)))

   (define-syntax-rule (check-kw-status test exp-status exp-req exp-kws)
     (let-values ([(status req kws) test])
       (check-eq?    status exp-status)
       (check-equal? req exp-req)
       (check-equal? kws exp-kws)))

   (test-case "procedure-keyword-status"
     (check-kw-status (procedure-keyword-status no-kw)   'none '()      '())
     (check-kw-status (procedure-keyword-status no-kw*)  'none '()      '())
     (check-kw-status (procedure-keyword-status req-kw)  'some '(#:key) '(#:key))
     (check-kw-status (procedure-keyword-status req-kw*) 'some '(#:key) '(#:key))
     (check-kw-status (procedure-keyword-status opt-kw)  'some '()      '(#:key))
     (check-kw-status (procedure-keyword-status opt-kw*) 'some '()      '(#:key))
     (check-kw-status (procedure-keyword-status all-kw)  'all  '()      #f)
     (check-kw-status (procedure-keyword-status all-kw*) 'all '()      #f)))

  (test-case "find-keyword-value"
    (check-equal? (find-keyword-value '#:a '()            '())        #f)
    (check-equal? (find-keyword-value '#:a '()            '()      0) 0)
    (check-equal? (find-keyword-value '#:a '(#:a #:b #:c) '(1 2 3))   1)
    (check-equal? (find-keyword-value '#:b '(#:a #:b #:c) '(1 2 3))   2)
    (check-equal? (find-keyword-value '#:c '(#:a #:b #:c) '(1 2 3))   3)
    (check-equal? (find-keyword-value '#:d '(#:a #:b #:c) '(1 2 3))   #f)
    (check-equal? (find-keyword-value '#:d '(#:a #:b #:c) '(1 2 3) 4) 4))

  (block
   (define-syntax-rule (check-kws-and-args test exp-kws exp-args)
     (let-values ([(kws args) test])
       (check-equal? kws exp-kws)
       (check-equal? args exp-args)))

   (test-case "merge-sorted-keyword-lists 1"
     (check-kws-and-args (merge-sorted-keyword-lists
                          '(#:a #:b #:c) '(1 2 3)
                          '()            '())
                         '(#:a #:b #:c) '(1 2 3))
     (check-kws-and-args (merge-sorted-keyword-lists
                          '()            '()
                          '(#:a #:b #:c) '(1 2 3))
                         '(#:a #:b #:c) '(1 2 3)))

   (test-case "merge-sorted-keyword-lists 2"
     (check-kws-and-args (merge-sorted-keyword-lists
                          '(#:a #:c)        '(a1 c1)
                          '(#:b)            '(b2))
                         '(#:a #:b #:c)     '(a1 b2 c1))
     (check-kws-and-args (merge-sorted-keyword-lists
                          '(#:a #:c)        '(a1 c1)
                          '(#:b #:d)        '(b2 d2))
                         '(#:a #:b #:c #:d) '(a1 b2 c1 d2)))

   (test-case "merge-sorted-keyword-lists 3"
     (check-kws-and-args (merge-sorted-keyword-lists
                          '(#:a #:b #:c)    '(a1 b1 c1)
                          '(#:b)            '(b2))
                         '(#:a #:b #:c)     '(a1 b1 c1))
     (check-kws-and-args (merge-sorted-keyword-lists
                          '(#:a #:b #:c)    '(a1 b1 c1)
                          '(#:b #:d)        '(b2 d2))
                         '(#:a #:b #:c #:d) '(a1 b1 c1 d2))
     (check-kws-and-args (merge-sorted-keyword-lists
                          '(#:a #:b #:c)    '(a1 b1 c1)
                          '(#:a #:b #:c)    '(a2 b2 c2))
                         '(#:a #:b #:c)     '(a1 b1 c1)))))

