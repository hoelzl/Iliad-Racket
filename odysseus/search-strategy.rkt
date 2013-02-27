#lang racket/base

(require racket/generic)
(require data/queue)

(provide result-strategy?
	 collect-result
	 result-sequence
	 result-list)
;;; Not sure whether we should provide the abbreviated names.
(provide ars ors nrs ars/pred ors/pred nrs/pred)
(provide (rename-out [ars all-results-strategy]
		     [ors one-result-strategy]
		     [nrs n-results-strategy]
		     [ars/pred all-results-satisfying-strategy]
		     [ors/pred one-result-satisfying-strategy]
		     [nrs/pred n-results-satisfying-strategy]))

(provide search-strategy?
	 result-strategy
	 next-node!
	 add-initial-node!
	 add-node!
	 add-nodes!
	 record-failure!)
(provide abstract-search-strategy)

;;; Result Strategies
;;; =================

(define-generics result-strategy
  ;; Collect result node and return #t if the computation should
  ;; continue, #f if the computation should stop
  (collect-result result-strategy result-node)
  ;; Return the result sequence collected so far by result strategy
  (result-sequence result-strategy)
  ;; Retrun the results collected so far as a list
  (result-list result-strategy))

;;; A strategy that collects all non-void results and always tries to
;;; continue the computation.
(struct ars ; all-results-strategy
  ([results #:auto])
  #:transparent
  #:auto-value (make-queue)
  #:methods gen:result-strategy
  [(define (collect-result strategy node)
     (unless (eq? node (void))
       (enqueue! (ars-results strategy)
		 node))
     #t)
   (define (result-sequence strategy)
     (ars-results strategy))
   (define (result-list strategy)
     (queue->list (result-sequence strategy)))])

;;; A strategy that collects a single non-void result and immediately
;;; stops the computation.
(struct ors ; one-result-strategy
  ([result #:mutable #:auto])
  #:transparent
  #:auto-value #f
  #:methods gen:result-strategy
  [(define (collect-result strategy node)
     (cond [(eq? node (void))
	    #t]
	   [else
	    (set-ors-result! strategy node)
	    #f]))
   (define (result-sequence strategy)
     (list (ors-result strategy)))
   (define (result-list strategy)
     (result-sequence strategy))])

;;; A strategy that collects all non-void results and stops the
;;; computation after n results have been collected.
(struct nrs ; n-results-strategy
  (results
   number-of-results
   number-of-results-so-far)
  #:transparent
  #:mutable
  #:omit-define-syntaxes
  #:constructor-name $nrs
  #:methods gen:result-strategy
  [(define (collect-result strategy node)
     (cond [(eq? node (void))
	    #t]
	   [else
	    (set-nrs-number-of-results-so-far!
	     strategy
	     (add1 (nrs-number-of-results-so-far strategy)))
	    (enqueue! (nrs-results strategy) node)
	    (< (nrs-number-of-results-so-far strategy)
	       (nrs-number-of-results strategy))]))
   (define (result-sequence strategy)
     (nrs-results strategy))
   (define (result-list strategy)
     (queue->list (result-sequence strategy)))])

(define (nrs [number-of-results 1])
  ($nrs (make-queue) number-of-results 0))


;;; A strategy that collects all results satisfying a predicate and
;;; always tries to continue the computation.
(struct ars/pred ; all-results-satisfying-strategy
  (results
   pred)
  #:transparent
  #:mutable
  #:omit-define-syntaxes
  #:constructor-name $ars/pred
  #:methods gen:result-strategy
  [(define (collect-result strategy node)
     (when ((ars/pred-pred strategy) node)
       (enqueue! (ars/pred-results strategy)
		 node))
     #t)
   (define (result-sequence strategy)
     (ars/pred-results strategy))
   (define (result-list strategy)
     (queue->list (result-sequence strategy)))])

(define (ars/pred predicate)
  ($ars/pred (make-queue) predicate))


;;; A strategy that collects a single result satisfying a predicate
;;; and immediately stops the computation.
(struct ors/pred ; one-result-satisfying-strategy
  (result
   pred)
  #:transparent
  #:mutable
  #:omit-define-syntaxes
  #:constructor-name $ors/pred
  #:methods gen:result-strategy
  [(define (collect-result strategy node)
     (cond [((ors/pred-pred strategy) node)
	    (set-ors/pred-result! strategy node)
	    #f]
	   [else
	    #t]))
   (define (result-sequence strategy)
     (list (ors/pred-result strategy)))
   (define (result-list strategy)
     (result-sequence strategy))])

(define (ors/pred predicate)
  ($ors/pred #f predicate))


;;; A strategy that collects all results that satisfy a predicate and
;;; stops the computation after n results have been collected.
(struct nrs/pred ; n-results-satisfying-strategy
  (results
   pred
   number-of-results
   number-of-results-so-far)
  #:transparent
  #:mutable
  #:omit-define-syntaxes
  #:constructor-name $nrs/pred
  #:methods gen:result-strategy
  [(define (collect-result strategy node)
     (cond [((nrs/pred-pred strategy) node)
	    (set-nrs/pred-number-of-results-so-far!
	     strategy
	     (add1 (nrs/pred-number-of-results-so-far strategy)))
	    (enqueue! (nrs/pred-results strategy) node)
	    (< (nrs/pred-number-of-results-so-far strategy)
	       (nrs/pred-number-of-results strategy))]
	   [else
	    #t]))
   (define (result-sequence strategy)
     (nrs/pred-results strategy))
   (define (result-list strategy)
     (queue->list (result-sequence strategy)))])

(define (nrs/pred predicate [number-of-results 1])
  ($nrs/pred (make-queue) predicate number-of-results 0))


;;; Search Strategies
;;; =================

(define-generics search-strategy
  ;; The result strategy employed by this search strategy
  (result-strategy search-strategy)
  ;; Return the next node, removing it from the stored nodes
  (next-node! search-strategy)
  ;; Add the initial node
  (add-initial-node! search-strategy node)
  ;; Add a single node
  (add-node! search-strategy node)
  ;; Add a sequence of nodes
  (add-nodes! search-strategy nodes)
  ;; Called by fail, mainly so that we can easily count the number of
  ;; failures, etc.
  (record-failure! search-strategy))

(struct abstract-search-strategy
  (result-strategy)
  #:transparent
  #:methods gen:search-strategy
  [(define (result-strategy strategy)
     (abstract-search-strategy-result-strategy strategy))]
  #:methods gen:result-strategy
  [(define/generic gen-collect-result collect-result)
   (define/generic gen-result-sequence result-sequence)
   (define/generic gen-result-list result-list)
   (define (collect-result strategy node)
     (gen-collect-result (result-strategy strategy) node))
   (define (result-sequence strategy)
     (gen-result-sequence (result-strategy strategy)))
   (define (result-list strategy)
     (gen-result-list (result-strategy strategy)))])
