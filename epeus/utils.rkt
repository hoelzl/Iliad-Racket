;;; Utilities for the Epeus object system.

;;; Written by Matthias Hölzl (tc@xantira.com)

;;; Utilities that are useful throughout the implementation of Epeus.

#lang racket

(require racket/performance-hint)
(require (only-in srfi/1 find every append-reverse))
(provide (all-from-out srfi/1))

;;;; Some Utilities
;;;; ==============

;;; Lists
;;; -----

(provide position-of)
(define (position-of elt lst)
  (let loop ([lst lst] [index 0])
    (cond [(empty? lst) #f]
	  [(eq? elt (first lst)) index]
	  [else (loop (rest lst) (add1 index))])))


;;; Exceptions
;;; ----------

(provide raise*)
;; This is a convenient function for raising exceptions
(define (raise* #:context-name [context-name #f] exn-maker fmt . args)
  (let ([fmt-num (- (length args) (procedure-arity exn-maker) -2)])
    (when (< fmt-num 0)
      (error 'raise* "got too few arguments"))
    (let loop ([fmt-args '()] [args args] [a fmt-num])
      (if (zero? a)
	  (raise (apply
		  exn-maker
		  (if context-name
		      (apply format (string-append "~s: " fmt)
			     context-name
			     (reverse fmt-args))
		      (apply format fmt
			     (reverse fmt-args)))
		  (current-continuation-marks) args))
	  (loop (cons (car args) fmt-args) (cdr args) (sub1 a))))))


;;; Utilities for Keywords and Keyword Procedures
;;; ---------------------------------------------

(provide keyword->symbol)
(define (keyword->symbol keyword)
  (string->symbol (keyword->string keyword)))

(provide procedure-accepts-keywords?)
(define (procedure-accepts-keywords? fun)
  (define-values (kws req-kws) (procedure-keywords fun))
  (not (and (null? kws) (null? req-kws))))

(provide find-keyword-value)
(define (find-keyword-value kw kws kw-args [default #f])
  (let loop ([kws kws] [kw-args kw-args])
    (cond [(null? kws) default]
          [(eq? kw (first kws))
           (first kw-args)]
          [else
           (loop (rest kws) (rest kw-args))])))

(provide merge-sorted-keyword-lists)
(define (merge-sorted-keyword-lists kws-1 kw-args-1 kws-2 kw-args-2)
  (let loop ([result-kws '()]
	     [result-kw-args '()]
	     [kws-1 kws-1]
	     [kw-args-1 kw-args-1]
	     [kws-2 kws-2]
	     [kw-args-2 kw-args-2])
    (cond [(null? kws-1)
	   (values
	    (append-reverse result-kws kws-2)
	    (append-reverse result-kw-args kw-args-2))]
	  [(null? kws-2)
	   (values
	    (append-reverse result-kws kws-1)
	    (append-reverse result-kw-args kw-args-1))]
	  ;; Use the value from kws-1 first when the keywords are equal
	  [(keyword<? (first kws-2) (first kws-1))
	   (loop (cons (first kws-2) result-kws)
		 (cons (first kw-args-2) result-kw-args)
		 kws-1
		 kw-args-1
		 (rest kws-2)
		 (rest kw-args-2))]
	  [else
	   (loop (cons (first kws-1) result-kws)
		 (cons (first kw-args-1) result-kw-args)
		 (rest kws-1)
		 (rest kw-args-1)
		 kws-2
		 kw-args-2)])))

(provide extract-allowed-keywords)
(define (extract-allowed-keywords actual-kws actual-kw-args allowed-kws)
  (let loop ([result-kws '()]
             [result-kw-args '()]
             [actual-kws actual-kws]
             [actual-kw-args actual-kw-args]
             [allowed-kws allowed-kws])
    (if (or (null? actual-kws) (null? allowed-kws))
        (values (reverse result-kws)
                (reverse result-kw-args))
        (let ([first-actual-kw (first actual-kws)]
              [first-allowed-kw (first allowed-kws)])
          (cond [(eq? first-actual-kw first-allowed-kw)
                 (loop (cons first-actual-kw result-kws)
                       (cons (first actual-kw-args) result-kw-args)
                       (rest actual-kws)
                       (rest actual-kw-args)
                       (rest allowed-kws))]
                [(keyword<? first-actual-kw first-allowed-kw)
                 (loop result-kws
                       result-kw-args
                       (rest actual-kws)
                       (rest actual-kw-args)
                       allowed-kws)]
                [else
                 (loop result-kws
                       result-kw-args
                       actual-kws
                       actual-kw-args
                       (rest allowed-kws))])))))

(provide initargs->hash)
(define (initargs->hash initargs)
  (let loop ([result (make-immutable-hasheq)]
             [initargs initargs])
    (if (null? initargs)
        result
        (let ([keyword (first initargs)])
          (unless (keyword? keyword)
            (error 'initargs->hash
                   (format "~a is not a valid initarg" keyword)))
          (define-values (value new-args)
            (let collect-values ([result '()]
                                 [args (rest initargs)])
              (if (or (null? args) (keyword? (first args)))
                  (cond [(null? result)
                         (values #t args)]
                        [(null? (rest result))
                         (values (first result) args)]
                        [else 
                         (values (reverse result) args)])
                  (collect-values (cons (first args) result)
                                  (rest args)))))
          (loop (hash-set result (keyword->symbol keyword) value)
                new-args)))))


;;;; Topological Sort and Utilities
;;;; ------------------------------

;; A simple topological sort.
;; It's in this file so that both TinyClos and Objects can use it.
;; This is a fairly modified version of code I (Gregor Kiczales --tc)
;; originally got from Anurag Mendhekar <anurag@moose.cs.indiana.edu>.
;;
(provide compute-std-cpl)
(define (compute-std-cpl c get-direct-supers)
  (top-sort (build-transitive-closure get-direct-supers c)
            (build-constraints get-direct-supers c)
            (std-tie-breaker get-direct-supers)))

;;; TODO: Define exception types and replace direct calls to `error'
;;; with `raise*'?

(provide top-sort)
(define (top-sort elements constraints tie-breaker)
  (let loop ([elements elements] [constraints constraints] [result '()])
    (if (null? elements)
	result
	(let ([can-go-in-now
	       (filter (lambda (x)
			 (every (lambda (constraint)
				  (or (not (eq? (second constraint) x))
				      (memq (first constraint) result)))
				constraints))
		       elements)])
	  (if (null? can-go-in-now)
	      (error 'top-sort "invalid constraints")
	      (let ([choice (if (null? (rest can-go-in-now))
				(first can-go-in-now)
				(tie-breaker result can-go-in-now))])
		(loop (filter (lambda (x) (not (eq? x choice))) elements)
		      constraints
		      (append result (list choice)))))))))

(define (std-tie-breaker get-supers)
  (lambda (partial-cpl min-elts)
    (let loop ([pcpl (reverse partial-cpl)])
      (let* ([current-elt (first pcpl)]
             [ds-of-ce (get-supers current-elt)]
             [common (filter (lambda (x) (memq x ds-of-ce)) min-elts)])
        (if (null? common)
	    (if (null? (rest pcpl))
		(error 'std-tie-breaker "nothing valid")
		(loop (rest pcpl)))
	    (first common))))))

(define (build-transitive-closure get-follow-ons x)
  (let track ([result '()] [pending (list x)])
    (if (null? pending)
	result
	(let ([next (first pending)])
	  (if (memq next result)
	      (track result (rest pending))
	      (track (cons next result)
		     (append (get-follow-ons next) (rest pending))))))))

(define (build-constraints get-follow-ons x)
  (let loop ([elements (build-transitive-closure get-follow-ons x)]
             [this-one '()]
             [result '()])
    (if (or (null? this-one) (null? (rest this-one)))
	(if (null? elements)
	    result
	    (loop (rest elements)
		  (cons (first elements) (get-follow-ons (first elements)))
		  result))
	(loop elements
	      (rest this-one)
	      (cons (list (first this-one) (second this-one)) result)))))


;;;; Miscellaneous
;;;; -------------

(provide ???)
(define ??? (letrec ([x x]) x))         ; Racket's #<undefined> value

(provide false-func)
(define false-func (lambda args #f))
