;;; Implementation of a CLOS-like object system for racket.

;;; Based on tiny-clos by Gregor Kizcales
;;; Heavily hacked by Eli Barzilay: Maze is Life!  (eli@barzilay.org)
;;; Converted to plain racket (V5), modifified and extended by
;;; Matthias Hölzl (tc@xantira.com)

;;; Original copyright:
;;; ***************************************************************************
;;; Copyright (c) 1992 Xerox Corporation.  All Rights Reserved.
;;;
;;; Use, reproduction, and preparation of derivative works are permitted.  Any
;;; copy of this software or of any derivative work must include the above
;;; copyright notice of Xerox Corporation, this paragraph and the one after it.
;;; Any distribution of this software or derivative works must comply with all
;;; applicable United States export control laws.
;;; This software is made available AS IS, and XEROX CORPORATION DISCLAIMS ALL
;;; WARRANTIES, EXPRESS OR IMPLIED, INCLUDING WITHOUT LIMITATION THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, AND
;;; NOTWITHSTANDING ANY OTHER PROVISION CONTAINED HEREIN, ANY LIABILITY FOR
;;; DAMAGES RESULTING FROM THE SOFTWARE OR ITS USE IS EXPRESSLY DISCLAIMED,
;;; WHETHER ARISING IN CONTRACT, TORT (INCLUDING NEGLIGENCE) OR STRICT
;;; LIABILITY, EVEN IF XEROX CORPORATION IS ADVISED OF THE POSSIBILITY OF SUCH
;;; DAMAGES.
;;; ***************************************************************************

#lang racket

(require racket/performance-hint)
(require (only-in srfi/1 find every append-reverse))
;;; For convenience; maybe import only required binding later
;;; (e.g., xor)
(require (for-syntax racket))
(require (for-syntax syntax/parse))


;;; Documentation from the original file:

;;; TODO: Update this and add it to the scribble documentation.  Most
;;; importantly, some functions now take racket keyword arguments
;;; instead of rest argument lists. --tc
;;;
;;; A very simple CLOS-like language, embedded in Scheme, with a simple MOP.
;;; The features of the default base language are:
;;;   * Classes, with instance slots, but no slot options.
;;;   * Multiple-inheritance.
;;;   * Generic functions with multi-methods and class specializers only.
;;;   * Primary methods and call-next-method; no other method combination.
;;;   * Uses Scheme's lexical scoping facilities as the class and generic
;;;     function naming mechanism.  Another way of saying this is that class,
;;;     generic function and methods are first-class (meta)objects.
;;;
;;; While the MOP is simple, it is essentially equal in power to both MOPs in
;;; AMOP.  This implementation is not at all optimized, but the MOP is designed
;;; so that it can be optimized.  In fact, this MOP allows better optimization
;;; of slot access extenstions than those in AMOP.
;;;
;;; In addition to calling a generic, the entry points to the default base
;;; language are:
;;;
;;;   (MAKE-CLASS name list-of-superclasses list-of-slot-names)
;;;   (MAKE-GENERIC-FUNCTION)
;;;   (MAKE-METHOD #:name [name '-anonymous-] list-of-specializers procedure)
;;;   (ADD-METHOD generic method)
;;;
;;;   (MAKE class . initargs)
;;;   (INITIALIZE instance initargs) ; Add methods to this, dont call directly.
;;;
;;;   (SLOT-REF    object slot-name)
;;;   (SLOT-SET!   object slot-name new-value)
;;;   (SLOT-BOUND? object slot-name)
;;;
;;; So, for example, one might do:
;;;   (define <position> (make-class '<position> (list <object>) (list 'x 'y)))
;;;   (add-method initialize
;;;     (make-method (list <position>)
;;;       (lambda (call-next-method pos initargs)
;;;         (for-each (lambda (initarg-name slot-name)
;;;                     (slot-set! pos slot-name
;;;                                (getarg initargs initarg-name 0)))
;;;                   '(x y)
;;;                   '(x y)))))
;;;   (set! p1 (make <position> 'x 1 'y 3))
;;;
;;; NOTE!  Do not use EQUAL? to compare objects!  Use EQ? or some hand written
;;;        procedure.  Objects have a pointer to their class, and classes are
;;;        circular structures, and...
;;;
;;; The introspective part of the MOP looks like the following.  Note that
;;; these are ordinary procedures, not generics.
;;;   * CLASS-OF
;;;     INSTANCE-OF?
;;;     SUBCLASS?
;;;   * CLASS-DIRECT-SUPERS
;;;     CLASS-DIRECT-SLOTS
;;;     CLASS-CPL
;;;     CLASS-SLOTS
;;;     CLASS-NAME
;;;   * GENERIC-METHODS
;;;     GENERIC-ARITY
;;;     GENERIC-NAME
;;;     GENERIC-COMBINATION
;;;   * METHOD-SPECIALIZERS
;;;     METHOD-PROCEDURE
;;;     METHOD-NAME
;;;
;;; The intercessory protocol looks like (generics in uppercase):
;;; ELI: All of these are generic functions now!
;;;   MAKE
;;;     ALLOCATE-INSTANCE
;;;     INITIALIZE                   (really a base-level generic)
;;;   class initialization
;;;     COMPUTE-CPL
;;;     COMPUTE-SLOTS
;;;     COMPUTE-GETTER-AND-SETTER
;;;   method initialization
;;;     COMPUTE-APPLY-METHOD
;;;   ADD-METHOD                    (Notice this is not a generic!) [eli: yes!]
;;;     COMPUTE-APPLY-GENERIC
;;;       COMPUTE-METHODS
;;;         COMPUTE-METHOD-MORE-SPECIFIC?
;;;       COMPUTE-APPLY-METHODS

;;;; Some Utilities
;;;; ==============

(define-syntax-rule (define-placeholder name)
  (define name (make <class> #:name 'name)))

(define-syntax-rule (define-placeholders name ...)
  (begin
    (define-placeholder name) ...))

(define-syntax-rule (define/macro name macro-name (args ...) body ...)
  (begin
    (define (name args ...)
      body ...)
    (define-syntax-rule (macro-name args ...)
      body ...)))

;;; Lists
;;; -----

(define (position-of elt lst)
  (let loop ([lst lst] [index 0])
    (cond [(empty? lst) #f]
	  [(eq? elt (first lst)) index]
	  [else (loop (rest lst) (add1 index))])))


;;; Exceptions
;;; ----------

(define-syntax-rule (provide-test-export id0 id ...)
  (module+ test-exports (provide id0 id ...)))

;;; OK, now let's get going.  But, as usual, before we can do anything
;;; interesting, we have to muck around for a bit first.  First, we need to
;;; load the support library.  [-- replaced with a module.]

(provide-test-export raise*)
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


;;; Utilities for Keywords
;;; ----------------------

(provide keyword->symbol)
(define (keyword->symbol keyword)
  (string->symbol (keyword->string keyword)))

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

(define-syntax-rule (make-keyword-procedure-0 proc)
  (procedure-reduce-keyword-arity
   (make-keyword-procedure proc)
   (arity-at-least 0)
   '()
   #f))

(define-syntax-rule (make-keyword-procedure-1 proc)
  (procedure-reduce-keyword-arity
   (make-keyword-procedure proc)
   (arity-at-least 1)
   '()
   #f))

(define-syntax-rule (make-keyword-procedure-n n proc)
  (procedure-reduce-keyword-arity
   (make-keyword-procedure proc)
   (arity-at-least n)
   '()
   #f))

;;; Utilities for Generics
;;; ----------------------

(define-syntax (generic->property-descriptor stx)
  (syntax-case stx ()
    [(_ id) (car (syntax-local-value #'id))]))

;;;; Topological Sort and Utilities
;;;; ------------------------------

;; A simple topological sort.
;; It's in this file so that both TinyClos and Objects can use it.
;; This is a fairly modified version of code I (Gregor Kiczales --tc)
;; originally got from Anurag Mendhekar <anurag@moose.cs.indiana.edu>.
;;
(define (compute-std-cpl c get-direct-supers)
  (top-sort (build-transitive-closure get-direct-supers c)
            (build-constraints get-direct-supers c)
            (std-tie-breaker get-direct-supers)))

;;; TODO: Define exception types and replace direct calls to `error'
;;; with `raise*'?

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


;;;; Instances
;;;; =========

;;; Then, we need to build what, in a more real implementation, would be the
;;; interface to the memory subsystem: instances and entities.  The former are
;;; used for instances of instances of <class>; the latter are used for
;;; instances of instances of <entity-class>.  In this MOP, none of this is
;;; visible to base- or MOP-level programmers.
;;; A few things to note, that have influenced the way all this is done:
;;;   - R4RS doesn't provide a mechanism for specializing the
;;;     behavior of the printer for certain objects.
;;;   - Some Scheme implementations bomb when printing circular structures --
;;;     that is, arrays and/or lists that somehow point back to themselves.
;;; So, the natural implementation of instances -- vectors whose first field
;;; point to the class -- is straight on out.  Instead, we use a procedure to
;;; `encapsulate' that natural representation.
;;; Having gone that far, it makes things simpler to unify the way normal
;;; instances and entities are handled, at least in the lower levels of the
;;; system.  Don't get faked out by this -- the user shouldn't think of normal
;;; instances as being procedures, they aren't. (At least not in this
;;; language.)  If you are using this to teach, you probably want to hide the
;;; implementation of instances and entities from people.

(define ??? (letrec ([x x]) x)) ; this is Racket's #<undefined> value
(define unspecified-initializer
  (make-keyword-procedure-0
   (lambda (kws kw-args . args)
     ???)))
(define false-func (lambda args #f))

;; Basic allocation follows, all was in a single let, but this is not needed
;; with Racket's modules.  Also modified to use simple structs for
;; everything, including entities since PLT has applicable struct objects.

;;; TODO: Add support for printing instances in a more meaningful way. 

;;; TODO: Define the following functions as generic functions
(define (print-object obj port mode)
  (define name (if (has-slot? obj 'name)
                   (slot-ref obj 'name)
                   '-unnamed-object-))
  (define the-class (class-of obj))
  (define the-class-name (and the-class (class-name the-class)))
  (cond [(has-slot? obj 'direct-supers)
         (define supers (slot-ref obj 'direct-supers))
         (define super-names (map class-name supers))
         (fprintf port "#{~a #:supers ~a #:class ~a}"
                  name super-names the-class-name)]
        [name
         (fprintf port "#{~a #:class ~a}"
                  name the-class-name)]
        [else
         (fprintf port "#{instance-of ~a}" the-class-name)]))

(define (object-equal? lhs rhs recursive-equal?)
  (equal?/recur lhs rhs recursive-equal?))

(define (object-hash obj recursive-equal-hash)
  (+ (recursive-equal-hash (instance-class obj))
     (recursive-equal-hash (instance-slots obj))))

(define (object-secondary-hash obj recursive-equal-hash)
    (+ (recursive-equal-hash (instance-class obj))
       (recursive-equal-hash (instance-slots obj))))

(define %the-instance-proc
  (make-keyword-procedure-1
   (lambda (kws kw-args o . args)
     (keyword-apply (instance-proc o) kws kw-args args))))

(provide instance?)
(define-values (struct:instance make-instance instance? inst-ref inst-set!)
  ;; slots: class, function, slots-vector
  (make-struct-type 'instance		; name
		    #f 			; super-type
		    3 			; init-field-cnt
		    0 			; auto-field-cnt
		    #f			; auto-value
		    (list		; props
		     (cons (generic->property-descriptor gen:custom-write)
			   (vector print-object))
		     (cons (generic->property-descriptor gen:equal+hash)
			   (vector object-equal? 
				   object-hash
				   object-secondary-hash))
		     ;; Note: need to define the procedure as
		     ;; property, not as direct (8th) argument to
		     ;; `make-struct-type', otherwise keyword
		     ;; arguments are not recognized.
		     (cons prop:procedure %the-instance-proc))
		    (current-inspector)))

(define-syntax-rule (instance-class x)
  (inst-ref x 0))
(define-syntax-rule (instance-proc  x)
  (inst-ref x 1))
(define-syntax-rule (instance-slots x)
  (inst-ref x 2))

;;; TODO: We should probably export some of these things in different
;;; modules, e.g., mop and mop-internals.
(provide set-instance-proc!) ; dangerous!

(define-syntax-rule (set-instance-class! x c)
  (inst-set! x 0 c))
(define-syntax-rule (set-instance-proc! x p)
  (inst-set! x 1 p))
(define-syntax-rule (set-instance-slots! x s)
  (inst-set! x 2 s))

(define-syntax-rule (%instance-ref o f)
  (vector-ref (instance-slots o) f))
(define-syntax-rule (%instance-set! o f n)
  (vector-set! (instance-slots o) f n))

(define (%allocate-instance class nfields)
  (make-instance class
                 (lambda args
                   (error 'instance
                          "an instance isn't a procedure -- can't apply it"))
                 (make-vector nfields ???)))

(define (%allocate-entity class nfields)
  (make-instance class
		 (lambda args
		   (error 'entity
			  "tried to call an entity before its proc is set"))
		 (make-vector nfields ???)))

;; Basic allocation ends here.

;; This is used only once as part of bootstrapping the braid.
(define (set-instance-class-to-self! class)
  (set-instance-class! class class))

(define object? instance?)


;;;; Slots
;;;; =====

;;; In contrast to the original tiny-clos we define slots as racket
;;; structures.  The properties of a slot are stored in the
;;; `slot-properties' hash table, keyed by symbols (not keywords).

(struct slot (name properties))

(define (make-slot-named name)
  (slot name (make-immutable-hasheq)))

(define (slot-property slot key [default #f])
  (when (keyword? key)
    (set! key (keyword->symbol key)))
  (hash-ref (slot-properties slot) key default))

(define (slot-allocation slot)
  (slot-property slot 'allocation))

(define (slot-valid-initargs slot)
  ;; TODO: Define protocol for other slot initargs?
  (define initarg (slot-property slot 'initarg))
  (if initarg (list initarg) null))

(define (merge-slots slots)
  (unless (pair? slots)
    (error 'merge-slots "argument must be a list of slots"))
  (when (null? slots)
    (error 'merge-slots "list of slots cannot be empty"))
  (define first-slot (first slots))
  (define other-slots (rest slots))
  (define name (slot-name first-slot))
  (unless (andmap (lambda (s)
                    (eq? (slot-name s) name))
                  other-slots)
    (error 'merge-slots "cannot merge different slots"))
  (define properties (slot-properties first-slot))
  (for ([other (in-list other-slots)])
    (for ([(property value) (in-hash (slot-properties other))])
      ;; TODO: Should probably call a generic `merge-properties' here
      ;; instead of overwriting the old value.
      (set! properties (hash-set properties property value))))
  (slot name properties))

;;;; Classes
;;;; =======


(define change-class!
  (procedure-reduce-keyword-arity
   (make-keyword-procedure
    (lambda (kws kw-args obj new-class)
      (let ([new (keyword-apply make kws kw-args new-class)]
            [new-slots (%class-slots new-class)])
        (for ([slot (in-list (%class-slots (class-of obj)))])
          ;; FIXME: Define a protocol to control which slot allocations
          ;; are actually allocated in instances and which ones are not
          (when (and (not (eq? 'class (slot-allocation slot)))
                     (assq (slot-name slot) new-slots))
            (slot-set! new (slot-name slot) (slot-ref obj (slot-name slot)))))
        (set-instance-slots! obj (instance-slots new))
        (set-instance-class! obj new-class))))
   2 '() #f))

;; This might be cute for some ugly hacks but not needed for now.
;; Copies the contents of source to target, making it an "alias" object.  This
;; is no re-provided by clos.rkt, but maybe it will in the future...
;; (define (copy-object-contents! target source)
;;   (set-instance-class! target (instance-class source))
;;   (set-instance-proc!  target (instance-proc  source))
;;   (set-instance-slots! target (instance-slots source)))

(define (class-of x)
  ;; This is an early version that will be modified when built-in types are
  ;; introduced later.
  (if (instance? x) (instance-class x) <top>))

;;; Now we can get down to business.  First, we initialize the braid.
;;; For bootstrapping, we define an early version of `make'.  It will
;;; be changed to the real version later on.
(define (make class 
	  #:direct-supers [dsupers '()]
	  #:direct-slots [dslots '()]
	  #:name [name '-anonymous-]
	  #:arity [arity #f]
	  #:specializers [specializers '()]
	  #:procedure [procedure #f]
	  #:qualifier [qualifier 'primary])
  (cond [(or (eq? class <class>) (eq? class <entity-class>))
         (define new (%allocate-instance class
					 (length the-slots-of-a-class)))
	 (define cpl (let loop ([sups dsupers] [so-far (list new)])
		       (if (null? sups)
			   (reverse so-far)
			   (loop (append (cdr sups)
					 (%class-direct-supers (car sups)))
				 (if (memq (car sups) so-far)
				     so-far
				     (cons (car sups) so-far))))))
	 (define slots
	   (apply append dslots (map %class-direct-slots (cdr cpl))))
	 (define nfields 0)
	 (define field-initializers '())
	 ;; this is a temporary allocator version, kept as the original
	 ;; one in tiny-clos.  the permanent version below is modified.
	 (define allocator
	   (lambda (init)
	     (let ([f nfields])
	       (set! nfields (+ nfields 1))
	       (set! field-initializers (cons init field-initializers))
	       (mcons (lambda (o)   (%instance-ref  o f))
		      (lambda (o n) (%instance-set! o f n))))))
	 (define getters-n-setters
	   (map (lambda (s)
		  (cons (slot-name s) (allocator unspecified-initializer)))
		slots))
	 (%set-class-direct-supers!      new dsupers)
	 (%set-class-direct-slots!       new dslots)
	 (%set-class-cpl!                new cpl)
	 (%set-class-slots!              new slots)
	 (%set-class-nfields!            new nfields)
	 (%set-class-field-initializers! new (reverse field-initializers))
	 (%set-class-getters-n-setters!  new getters-n-setters)
	 (%set-class-name!               new name)
	 (%set-class-initializers!       new '()) ; no class inits now
	 (%set-class-valid-initargs!     new #f)  ; no initargs now
	 new]
        [(eq? class <generic>)
         (let ([new   (%allocate-entity class (length (%class-slots class)))])
           (%set-generic-methods!     new '())
           (%set-generic-arity!       new arity)
           (%set-generic-name!        new name)
           (%set-generic-combination! new #f)
           new)]
        [(eq? class <method>)
         (let ([new  (%allocate-entity class (length (%class-slots class)))])
           (%set-method-specializers! new specializers)
           (%set-method-procedure!    new procedure)
           (%set-method-qualifier!    new qualifier)
           (%set-method-name!         new name)
           (set-instance-proc!        new (method:compute-apply-method #f new))
           new)]))

;;; These are the real versions of slot-ref and slot-set!.  Because of the way
;;; the new slot access protocol works, with no generic call in line, they can
;;; be defined up front like this.  Cool eh?

(define/macro slot-ref %slot-ref (object slot-name)
  ((lookup-slot-info (class-of object) slot-name mcar) 
   object))

(define/macro slot-set! %slot-set! (object slot-name new-value)
  ((lookup-slot-info (class-of object) slot-name mcdr)
   object new-value))

(define set-slot-ref! slot-set!)

;; This is a utility that is used to make locked slots
(define (lock-setter! g+s key error)
  (let ([getter (mcar g+s)]
	[setter (mcdr g+s)])
    (set-mcdr! g+s
	       (lambda (o n)
		 (cond [(and (pair? n) (eq? key (car n)) (not (eq? key #t)))
			(setter o (cdr n))]
		       [(eq? ??? (getter o)) (setter o n)]
		       [else (error)])))))

(define (has-slot? object slot-name)
  (and (assq slot-name
             (%class-getters-n-setters (class-of object)))
       #t))

(define (slot-bound? object slot-name)
  (not (eq? ??? (%slot-ref object slot-name))))

(define (lookup-slot-info class slot-name selector)
  (define getter-n-setter
    (assq slot-name (%class-getters-n-setters class)))
  (if getter-n-setter
      (selector (cdr getter-n-setter))
      (raise* make-exn:fail:contract
	      "slot-ref: no slot `~.s' in ~.s"
	      slot-name class)))

;;; These are for optimizations - works only for single inheritance!
(define (%slot-getter class slot-name)
  (lookup-slot-info class slot-name mcar))
(define (%slot-setter class slot-name)
  (lookup-slot-info class slot-name mcdr))


;;; TODO: Change singletons to structs

;;; Singleton class.  A hash-table is used so it is still possible to compare
;;; classes with eq?.
(define singleton-classes (make-weak-hasheq))

(define (singleton x)
  (or (hash-ref singleton-classes x #f)
      (let ([c (list 'singleton x)])
        (hash-set! singleton-classes x c)
        c)))

(define/macro singleton? %singleton? (x)
  (and (pair? x) (eq? (car x) 'singleton)))

(define singleton-value cadr)


(define struct-to-class-table (make-hasheq))
(define (struct-type->class stype)
  (hash-ref
   struct-to-class-table stype
   (thunk
    (let-values ([(name init-field-k auto-field-k accessor mutator
			immutable-k-list super skipped?)
		  (struct-type-info stype)])
      (let* ([supers (list (cond [super (struct-type->class super)]
				 [skipped? <opaque-struct>]
				 [else <struct>]))]
	     [proc? (procedure-struct-type? stype)]
	     [supers (if proc? (cons <primitive-procedure> supers) supers)]
	     [this (parameterize ([*default-object-class* #f])
		     (make (if proc? <procedure-class> <primitive-class>)
		       #:name name #:direct-supers supers))])
	(hash-set! struct-to-class-table stype this)
	this)))))

(define (class-direct-slots       c) (%slot-ref c 'direct-slots))
(define (class-direct-supers      c) (%slot-ref c 'direct-supers))
(define (class-slots              c) (%slot-ref c 'slots))
(define (class-nfields            c) (%slot-ref c 'nfields))
(define (class-field-initializers c) (%slot-ref c 'field-initializers))
(define (class-getters-n-setters  c) (%slot-ref c 'getters-n-setters))
(define (class-cpl                c) (%slot-ref c 'cpl))
(define (class-name               c) (%slot-ref c 'name))
(define (class-initializers       c) (%slot-ref c 'initializers))
(define (class-valid-initargs     c) (%slot-ref c 'valid-initargs))
(define (generic-methods          g) (%slot-ref g 'methods))
(define (generic-arity            g) (%slot-ref g 'arity))
(define (generic-name             g) (%slot-ref g 'name))
(define (generic-combination      g) (%slot-ref g 'combination))
(define (method-specializers      m) (%slot-ref m 'specializers))
(define (method-procedure         m) (%slot-ref m 'procedure))
(define (method-qualifier         m) (%slot-ref m 'qualifier))
(define (method-name              m) (%slot-ref m 'name))
(define (method-arity m)
  (let ([a (procedure-arity (%method-procedure m))])
    (cond [(integer? a) (sub1 a)]
          [(arity-at-least? a)
           ;; keyword-procedures always return (arity-at-least 0)...
           (if (zero? (arity-at-least-value a))
               (make-arity-at-least 0)
               (make-arity-at-least (sub1 (arity-at-least-value a))))]
          [else (error 'method-arity "the procedure in ~.s has bad arity ~e"
                       m a)])))

;;; These versions will be optimized later.
(define %class-direct-slots       class-direct-slots)
(define %class-direct-supers      class-direct-supers)
(define %class-slots              class-slots)
(define %class-nfields            class-nfields)
(define %class-field-initializers class-field-initializers)
(define %class-getters-n-setters  class-getters-n-setters)
(define %class-cpl                class-cpl)
(define %class-name               class-name)
(define %class-initializers       class-initializers)
(define %class-valid-initargs     class-valid-initargs)
(define %generic-methods          generic-methods)
(define %generic-arity            generic-arity)
(define %generic-name             generic-name)
(define %generic-combination      generic-combination)
(define %method-specializers      method-specializers)
(define %method-procedure         method-procedure)
(define %method-qualifier         method-qualifier)
(define %method-name              method-name)

(define (%set-class-direct-slots!   c x) (%slot-set! c 'direct-slots   x))
(define (%set-class-direct-supers!  c x) (%slot-set! c 'direct-supers  x))
(define (%set-class-slots!          c x) (%slot-set! c 'slots          x))
(define (%set-class-nfields!        c x) (%slot-set! c 'nfields        x))
(define (%set-class-field-initializers! c x)
  (%slot-set! c 'field-initializers x))
(define (%set-class-getters-n-setters! c x)
  (%slot-set! c 'getters-n-setters x))
(define (%set-class-cpl!            c x) (%slot-set! c 'cpl            x))
(define (%set-class-name!           c x) (%slot-set! c 'name           x))
(define (%set-class-initializers!   c x) (%slot-set! c 'initializers   x))
(define (%set-class-valid-initargs! c x) (%slot-set! c 'valid-initargs x))
(define (%set-generic-methods!      g x) (%slot-set! g 'methods        x))
(define (%set-generic-arity!        g x) (%slot-set! g 'arity          x))
(define (%set-generic-name!         g x) (%slot-set! g 'name           x))
(define (%set-generic-combination!  g x) (%slot-set! g 'combination    x))
(define (%set-method-specializers!  m x) (%slot-set! m 'specializers   x))
(define (%set-method-procedure!     m x) (%slot-set! m 'procedure      x))
(define (%set-method-qualifier!     m x) (%slot-set! m 'qualifier      x))
(define (%set-method-name!          m x) (%slot-set! m 'name           x))

;;; These are used to access the two slots that optimize generic invocations.
(define (%generic-app-cache            g  ) (%slot-ref  g 'app-cache))
(define (%generic-singletons-list      g  ) (%slot-ref  g 'singletons-list))
(define (%set-generic-app-cache!       g x) (%slot-set! g 'app-cache x))
(define (%set-generic-singletons-list! g x) (%slot-set! g 'singletons-list x))


;;; The next 7 clusters define the 6 initial classes.  It takes 7 to 6 because
;;; the first and fourth both contribute to <class>.

(define the-slots-of-a-class
  '(direct-supers              ; (class ...)
    direct-slots               ; ((slot name properties) ...)
    cpl                        ; (class ...)
    slots                      ; ((name . options) ...)
    nfields                    ; an integer
    field-initializers         ; (proc ...)
    getters-n-setters          ; ((slot-name getter setter) ...)
    name                       ; a symbol
    initializers               ; (proc ...)
    valid-initargs))           ; (initarg ...) or #f

(define getters-n-setters-for-class ; see lookup-slot-info
  (map (lambda (s)
         (let ([f (position-of s the-slots-of-a-class)])
           (cons s (mcons (lambda (o)   (%instance-ref  o f))
                          (lambda (o n) (%instance-set! o f n))))))
       the-slots-of-a-class))

(define <class> (%allocate-instance #f (length the-slots-of-a-class)))
(set-instance-class-to-self! <class>)


;; In the original tiny-clos, this block used to just set the getters-n-setters
;; slot of a class to '() since it wasn't used anyway.  In Swindle the MOP
;; accessors are all optimized to directly get the vector element because the
;; meta hierarchy is assumed to be single-inheritance only (allocation of more
;; slots always come after the built in ones), so what I do here is set the
;; slot value properly, and since `%class-getters-n-setters' accesses the
;; vector directly it doesn't go through slot-ref, which means that the
;; slot-ref definition above is fine. So,
;;   (%set-class-getters-n-setters! <class> getters-n-setters-for-class)
;; translates into this:
(define bootstrap-getters-n-setters
  (cdr (assq 'getters-n-setters getters-n-setters-for-class)))
(define bootstrap-%set-class-getters-n-setters!
  (mcdr bootstrap-getters-n-setters))
(define bootstrap-%get-class-getters-n-setters
  (mcar bootstrap-getters-n-setters))

(bootstrap-%set-class-getters-n-setters!
 <class> getters-n-setters-for-class)
;; and now the direct `%class-getters-n-setters' version:
(set! %class-getters-n-setters
      bootstrap-%get-class-getters-n-setters)

(define <top> (make <class>
		#:name          '<top>
		#:direct-supers '()
		#:direct-slots  '()))

(define <object> (make <class>
		   #:name          '<object>
		   #:direct-supers (list <top>)
		   #:direct-slots  '()))

;;; This cluster, together with the first cluster above that defines <class>
;;; and sets its class, have the effect of:
;;;   (define <class>
;;;     (make <class> #:name          '<class>
;;;                   #:direct-supers (list <object>)
;;;                   #:direct-slots  '(direct-supers ...)))
(%set-class-direct-supers!      <class> (list <object>))
(%set-class-cpl!                <class> (list <class> <object> <top>))
(%set-class-direct-slots!       <class> (map make-slot-named
					     the-slots-of-a-class))
(%set-class-slots!              <class> (map make-slot-named
					     the-slots-of-a-class))
(%set-class-nfields!            <class> (length the-slots-of-a-class))
(%set-class-field-initializers! <class> (map (lambda (s)
                                               unspecified-initializer)
                                             the-slots-of-a-class))
(%set-class-name!               <class> '<class>)
(%set-class-initializers!       <class> '())
(%set-class-valid-initargs!     <class> #f)

(define <procedure-class>
  (make <class>
    #:name          '<procedure-class>
    #:direct-supers (list <class>)
    #:direct-slots  '()))

(define <entity-class>
  (make <class>
    #:name          '<entity-class>
    #:direct-supers (list <procedure-class>)
    #:direct-slots  '()))

(define <function>
  (make <class>
    #:name          '<function>
    #:direct-supers (list <top>)
    #:direct-slots  '()))

;;; The two extra slots below (app-cache and singletons-list) are used to
;;; optimize generic invocations: app-cache holds an 'equal hash-table that
;;; maps a list of classes to the lambda expression that holds the method call
;;; (it used to be an l-hash-table, but 'equal is ok since we can't compare
;;; swindleobj instances recursively -- which is also why tool.rkt needs to
;;; redefine the `render-value/format' method).  The contents of this slot is
;;; reset whenever a method is added to the generic.  Two problems make things
;;; a little more complicated.  First, if add-method is used to modify any of
;;; the generic-invocation-generics then all of these caches should be flushed,
;;; this is achieved by setting *generic-app-cache-tag* to a new [list] object
;;; and the value of app-cache is a cons of that value and the actual hash
;;; table - if we see that the car is not eq? to the current tag, then we flush
;;; the cache.  Second, singleton values might screw things up, so we hold in
;;; singletons-list a list that has the same length as all method specializer
;;; lists, each element contains a hash table with all singleton values that
;;; appear in that place matched to #t, then when we try to see if we have a
;;; cached function for a generic application, we scan the argument list
;;; against this list, and any value that has a singleton with that value at
;;; some method, is left in place for the app-cache lookup (it is used itself
;;; rather than its class).  This whole thing is a bit complicated but leads to
;;; dramatic run-time improvement.

(define <generic>
  (make <entity-class>
    #:direct-supers (list <object> <function>)
    #:direct-slots  (map make-slot-named
			 '(methods arity name combination
				   app-cache singletons-list)) ; see above
    #:name          '<generic>))

(define <method>
  (make <entity-class>
    #:direct-supers (list <object> <function>)
    #:direct-slots  (map make-slot-named
			 '(specializers procedure qualifier name))
    #:name          '<method>))

;; Do this since compute-apply-method relies on them not changing, as well as a
;; zillion other places.  A method should be very similar to a lambda.
(for ([slot (in-list '(specializers procedure qualifier))])
  (lock-setter! (lookup-slot-info <method> slot values)
		#t
		(lambda ()
		  (raise* make-exn:fail:contract
			  "slot-set!: slot `~.s' in <method> is locked" slot))))

;;; Default values
;;; --------------

;;; Having defined the necessary classes, we can now introduce
;;; parameters for default values.

(define *default-class-class*       (make-parameter <class>))
(define *default-entityclass-class* (make-parameter <entity-class>))
(define *default-method-class*      (make-parameter <method>))
(define *default-generic-class*     (make-parameter <generic>))

(define *default-object-class* (make-parameter #f))


(define (make-class [name '-anonymous-]
		    [direct-supers (list <object>)]
		    [direct-slots '()])
  (make <class>
    #:name name
    #:direct-supers direct-supers
    #:direct-slots  direct-slots))

(define (make-generic-function [name '-anonymous-] [arity #f])
  (make <generic> #:name name #:arity arity))

(define (make-method #:name [name '-anonymous-] specializers procedure)
  (make <method>
    #:name name
    #:specializers specializers
    #:procedure    procedure))

(define no-next-method       (make-generic-function 'no-next-method))
(define no-applicable-method (make-generic-function 'no-applicable-method))

;;; TODO: How should we handle keyword arguments in the following
;;; methods?

;;; Add possibility of generic-independent method application - this is the
;;; instance-proc of methods, which is activated when you apply the object (in
;;; the original, methods could not be applied).  This is defined using this
;;; name and arguments because it is later used directly by the generic
;;; function (cannot use the generic in the initial make since methods need to
;;; be created when the generics are constructed).

(define (method:compute-apply-method call-next-method method)
  ;; (printf "method:compute-apply-method\n")
  (let* ([specializers (%method-specializers method)]
         [*no-next-method* ; see the *no-next-method* trick below
          (make-keyword-procedure-0
           (lambda (kws kw-args . args)
             (apply no-next-method #f method kws kw-args args)))]
         [proc     (%method-procedure method)]
         [arity    (method-arity method)]
         [exact?   (integer? arity)]
         [required ((if exact? identity arity-at-least-value) arity)])
    (when (and exact? (> (length specializers) required))
      (error 'compute-apply-method
             "got ~e specializers for ~s - too many for procedure arity ~a"
             (length specializers) (%method-name method) required))
    ;;; TODO: Check keyword args
    (make-keyword-procedure-0
     (lambda (kws kw-args . args)
       ;; (printf "applying method ~a\n" (method-name method))
       (cond [(if exact?
		  (not (= (length args) required))
		  (< (length args) required))
	      (raise* make-exn:fail:contract:arity
		      "method ~a: expects ~a~e argument~a, given ~e~a"
		      (%method-name method)
		      (if exact? "" "at least ") required
		      (if (= 1 required) "" "s") (length args)
		      (if (null? args) "" (format ": ~e" args)))]
	     [(not (every instance-of? args specializers))
	      (let loop ([args args] [specs specializers])
		(if (instance-of? (car args) (car specs))
		    (loop (cdr args) (cdr specs))
		    (raise* make-exn:fail:contract
			    "method ~a: expects argument of type ~a; given ~e"
			    (%method-name method) (%class-name (car specs))
			    (car args))))]
	     [else (keyword-apply proc kws kw-args *no-next-method* args)])))))

(define allocate-instance
  (make-generic-function 'allocate-instance))

(define initialize
  (make-generic-function 'initialize))

(define compute-getter-and-setter
  (make-generic-function 'compute-getter-and-setter))

(define compute-cpl
  (make-generic-function 'compute-cpl))

(define compute-slots
  (make-generic-function 'compute-slots))

(define compute-apply-method
  (make-generic-function 'compute-apply-method))

(define compute-apply-generic
  (make-generic-function 'compute-apply-generic))

(define compute-methods
  (make-generic-function 'compute-methods))

(define compute-method-more-specific?
  (make-generic-function 'compute-method-more-specific?))

(define compute-apply-methods
  (make-generic-function 'compute-apply-methods))

;;; The next thing to do is bootstrap generic functions.

(define generic-invocation-generics
  (list compute-apply-generic compute-methods
        compute-method-more-specific? compute-apply-methods))

;;; This is used to signal whenever all method caches are to be reset - so when
;;; a method is added to generic-invocation-generics, this is set to some value
;;; which is not eq? to the current one.
(define *generic-app-cache-tag* #t)

(define (add-method generic method)
  ;; add singleton specializer value (if any) to the corresponding hash table
  ;; in singletons-list.
  (define (add-to-singletons-list specs tables)
    ;; (printf "add-to-singletons-list\n")
    (cond
     [(null? specs) null]
     [(%singleton? (car specs))
      (let ([ht (or (car tables)
                    (make-weak-hasheq))])
        (hash-set! ht (singleton-value (car specs)) #t)
        (cons ht (add-to-singletons-list (cdr specs) (cdr tables))))]
     [else
      (cons (car tables)
            (add-to-singletons-list (cdr specs) (cdr tables)))]))
  (define (n-falses n)
    ;; (printf "n-falses\n")
    (let loop ([n n] [r '()]) (if (zero? n) r (loop (sub1 n) (cons #f r)))))
  (let ([tables    (%generic-singletons-list generic)]
        [specs     (%method-specializers method)]
        [qualifier (%method-qualifier method)])
    ;; make sure that tables always contain enough hash tables (or #f's)
    ;; (printf "add-method ~a\n" (generic-name generic))
    (cond [(eq? tables ???)
           (set! tables (n-falses (length specs)))]
          [(< (length tables) (length specs))
           (set! tables (append
                         tables
                         (n-falses (- (length specs) (length tables)))))])
    ;; (printf "add-method: 1\n")
    (set! tables (add-to-singletons-list specs tables))
    ;; (printf "add-method: 2\n")
    (%set-generic-singletons-list! generic tables)
    ;; (printf "add-method: 3\n")
    (if (memq generic generic-invocation-generics)
        ;; reset all caches by changing the value of *generic-app-cache-tag*
        (set! *generic-app-cache-tag* (list #f))
        ;; reset this generic app-cache
        (%set-generic-app-cache! generic ???))
    ;; (printf "add-method 4\n")
    (%set-generic-methods!
     generic
     (cons method
           (filter (lambda (m)
                     (not (and (= (length (method-specializers m)) (length specs))
                               (every eq? (method-specializers m) specs)
                               (eq? (%method-qualifier m) qualifier))))
                   (%generic-methods generic))))
    ;; (printf "add-method 5\n")
    (set-instance-proc! generic (compute-apply-generic generic))))

;;; Adding a method calls COMPUTE-APPLY-GENERIC, the result of which calls the
;;; other generics in the generic invocation protocol.  Two, related, problems
;;; come up.  A chicken and egg problem and a infinite regress problem.
;;; In order to add our first method to COMPUTE-APPLY-GENERIC, we need
;;; something sitting there, so it can be called.  The first definition below
;;; does that.
;;; Then, the second definition solves both the infinite regress and the not
;;; having enough of the protocol around to build itself problem the same way:
;;; it special cases invocation of generics in the invocation protocol.

(set-instance-proc!
 compute-apply-generic
 (lambda (generic)
   ;; (printf "compute-apply-generic (bootstrap)\n")
   ((%method-procedure (car (%generic-methods generic))) '() generic)))

(add-method 
 compute-apply-generic
 (make-method #:name "{compute-apply-generic <generic>}"
  (list <generic>)
  (lambda (call-next-method generic)
    ;; (printf "compute-apply-generic ~a\n" (generic-name generic))
    ;; This function converts the list of arguments to a list of keys to look
    ;; for in the cache - use the argument's class except when there is a
    ;; corresponding singleton with the same value at the same position.
    (define (get-keys args tables)
      ;; (printf "get-keys\n")
      (let loop ([args args] [tables tables] [ks '()])
        (if (or (null? tables) (null? args))
            (reverse ks)
            (loop (cdr args) (cdr tables)
                  (cons (if (and (car tables)
                                 (hash-ref
                                  (car tables) (car args) false-func))
                            (car args)
                            (class-of (car args)))
                        ks)))))
    ;; This is the main function that brings the correct value from the
    ;; cache, or generates one and store it if there is no entry, or the
    ;; cache was reset.  Finally, it is applied to the arguments as usual.
    ;; NOTE: This code is delicate! Handle with extreme care!
    (make-keyword-procedure-0
     (lambda (kws kw-args . args)
       ;; (printf "applying generic ~a\n" (generic-name generic))
       (let ([app-cache (%generic-app-cache generic)]
             [arity     (%generic-arity generic)]
             [keys      (get-keys args (%generic-singletons-list generic))]
             [ground?   (and ;* Ground case
                         (memq generic generic-invocation-generics)
                         (pair? args)
                         (memq (car args) generic-invocation-generics))])
         ;; This function creates the cached closure -- the assumption is that
         ;; `keys' contain a specification that will identify all calls that
         ;; will have this exact same list.
         ;; TODO: Include keyword args here!
         ;; (printf "applying generic: computed caches\n")
         (define (compute-callable)
           ;; (printf "compute-callable\n")
           (let ([c (if ground?
                        (let ([m (%method-procedure
                                  (last (%generic-methods generic)))])
                          (make-keyword-procedure-0
                           (lambda (kws kw-args . args)
                             (keyword-apply m kws kw-args #f args))))
                        (compute-apply-methods
                         generic (compute-methods generic args)))])
             (hash-set! (cdr app-cache) keys c)
             c))
         ;; TODO: checks for keyword args
         ;; (printf "applying generic: arity checks\n")
         (when (cond [(not arity) #f]
                     [(integer? arity) (not (= (length args) arity))]
                     [else (< (length args) (arity-at-least-value arity))])
           (let ([least (and (arity-at-least? arity)
                             (arity-at-least-value arity))])
             (raise* make-exn:fail:contract:arity
                     "generic ~a: expects ~a~e argument~a, given ~e~a"
                     (%generic-name generic)
                     (if least "at least " "") (or least arity)
                     (if (= 1 (or least arity)) "" "s") (length args)
                     (if (null? args) "" (format ": ~e" args)))))
         ;; (printf "applying generic: performed arity checks\n")
         (when (or (eq? app-cache ???)
                   (not (eq? (car app-cache) *generic-app-cache-tag*)))
           ;; (printf "applying generic: invalidating app cache\n")
           (set! app-cache (cons *generic-app-cache-tag*
                                 (make-weak-hash)))
           (%set-generic-app-cache! generic app-cache))
         ;; (printf "applying method: extracting method from app cache: ~a\n" keys)
         (define real-method (hash-ref (cdr app-cache) keys compute-callable))
         ;; (printf "applying generic: calling keyword-apply\n")
         (keyword-apply real-method kws kw-args args)))))))

(add-method compute-methods
  (make-method #:name "{compute-methods <generic>}"
    (list <generic>)
    (lambda (call-next-method generic args)
      (printf "compute-methods\n")
      (define more-specific-for-args? (compute-method-more-specific? generic))
      (define nargs (length args))
      (sort (filter
             (lambda (m)
               ;; Note that every only goes as far as the shortest list
               (and
                (procedure-arity-includes? m nargs)
                (every instance-of? args (%method-specializers m))))
             (%generic-methods generic))
            (lambda (m1 m2) (more-specific-for-args? m1 m2 args))))))

(add-method compute-method-more-specific?
  (make-method #:name "{method-more-specific <generic>}"
    (list <generic>)
    (lambda (call-next-method generic)
      (printf "compute-method-more-specific?\n")
      (lambda (m1 m2 args)
        (let loop ([specls1 (%method-specializers m1)]
                   [specls2 (%method-specializers m2)]
                   [args    args])
          (cond [(and (null? specls1) (null? specls2))
                 (if (eq? (%method-qualifier m1) (%method-qualifier m2))
		     (error 'generic
			    "two methods are equally specific in ~e" generic)
		     #f)]
                ;; some methods in this file have fewer specializers than
                ;; others, for things like args -- so remove this, leave the
                ;; args check but treat the missing as if it's <top>
                ;; ((or (null? specls1) (null? specls2))
                ;;  (error 'generic
                ;;         "two methods have different number of ~
                ;;          specializers in ~e" generic))
                [(null? args) ; shouldn't happen
                 (error 'generic
                        "fewer arguments than specializers for ~e" generic)]
                [(null? specls1) ; see above -> treat this like <top>
                 (if (eq? <top> (car specls2))
		     (loop specls1 (cdr specls2) (cdr args))
		     #f)]
                [(null? specls2) ; see above -> treat this like <top>
                 (if (eq? <top> (car specls1))
		     (loop (cdr specls1) specls2 (cdr args))
		     #t)]
                [else (let ([c1 (car specls1)] [c2 (car specls2)])
                        (if (eq? c1 c2)
			    (loop (cdr specls1) (cdr specls2) (cdr args))
			    (more-specific? c1 c2 (car args))))]))))))

(add-method compute-apply-methods
  (make-method #:name "{compute-apply-methods <generic>}"
    (list <generic>)
    (lambda (call-next-method generic methods)
      (printf "compute-apply-methods ~a\n" (generic-name generic))
      (let ([primaries '()] [arounds '()] [befores '()] [afters '()]
	    [combination (%generic-combination generic)])
	(define-syntax (let-args stx)
	  (syntax-parse stx
	    [(_ ([kws:id  new-kws:id]
		 [kw-args:id new-kw-args:id]
		 [args:id new-args:id])
		body:expr ...+)
	     (syntax-protect
	      #'(begin
		  (when (xor (null? new-kws) (null? new-kw-args))
		    (error 'compute-apply-methods
			   "~e and ~e must both be null or non-null"
			   new-kws new-kw-args))
                  (printf "compute-apply-methods: ~a, ~a\n" kws new-kws)
		  (let-values ([(kws kw-args)
				(merge-sorted-keyword-lists
                                 kws kw-args new-kws new-kw-args)])
		    (let ([args (if (null? new-args) args new-args)])
		      body ...))))]))
	;; TODO: This comment does not seem to be relevant anymore... --tc
	;; *** Trick: this (and in <method> above) is the only code that is
	;; supposed to ever apply a method procedure.  So, the closure that
	;; will invoke `no-next-method' is named `*no-next-method*' so it is
	;; identifiable.  The only way to break this would be to call the
	;; method-procedure directly on an object with such a name.
	(define one-step
	  (if combination
	      (combination generic)
	      (lambda (tail kws kw-args args)
		;; tail is never null: (null? (cdr tail)) below, and the fact
		;; that this function is applied on the primaries which are
		;; never null
		(make-keyword-procedure-0
		 (lambda (new-kws new-kw-args . new-args)
		   (let-args ([kws new-kws]
			      [kw-args new-kw-args]
			      [args new-args])
		     (keyword-apply
		      (cdar tail) kws kw-args
		      (if (null? (cdr tail))
                          (make-keyword-procedure-0
                           (lambda (kws kw-args . args)
                             (apply no-next-method generic (caar tail)
                                    kws kw-args args)))
			  (one-step (cdr tail) kws kw-args args))
		      args)))))))

	(define ((apply-before/after-method kws kw-args args) method)
          (keyword-apply (cdr method) kws kw-args
                         (make-keyword-procedure-0
                          (lambda (kws kw-args . args)
                            (apply no-next-method generic (car method)
                                   kws kw-args args)))
                         args))

	(define (call-before-primary-after kws kw-args args)
	  (make-keyword-procedure-0
	   (lambda (new-kws new-kw-args . new-args)
	     ;; could supply newargs below, but change before calling befores
	     (let-args ([kws new-kws]
			[kw-args new-kw-args]
			[args new-args])
	       (for-each (apply-before/after-method kws kw-args args) befores)
	       (begin0 ((one-step primaries args))
		 (for-each (apply-before/after-method args) afters))))))

        (define (one-around-step tail kws kw-args args)
          (if (null? tail)
              (call-before-primary-after kws kw-args args)
              (make-keyword-procedure-0
               (lambda (new-kws new-kw-args . new-args)
                 (let-args ([kws new-kws]
                            [kw-args new-kw-args]
                            [args new-args])
                   (keyword-apply (cdar tail) kws kw-args
                                  (one-around-step (cdr tail) args) args))))))
        ;; first sort by qualifier and pull out method-procedures
        (let loop ([ms methods])
          (unless (null? ms)
            (let-syntax ([push! (syntax-rules ()
                                  [(_  p)
                                   (set! p (cons (cons (car ms)
                                                       (%method-procedure (car ms)))
                                                 p))])])
              (case (%method-qualifier (car ms))
                [(primary) (push! primaries)]
                [(around)  (push! arounds)]
                [(before)  (push! befores)]
                [(after)   (push! afters)]
                ;; ignore other qualifiers
                ;; [else (error 'compute-apply-methods
                ;;              "a method ~e has an unexpected qualifier `~e'"
                ;;              (car methods)
                ;;              (%method-qualifier (car methods)))]
                )
              (loop (cdr ms)))))
        (set! primaries (reverse primaries))
        (set! arounds   (reverse arounds))
        (set! befores   (reverse befores))
        ;; no reverse for afters
        (cond [(null? primaries)
               (lambda args (apply no-applicable-method generic args))]
              ;; optimize common case of only primaries
              [(and (null? befores) (null? afters) (null? arounds))
               ;; args is initialized to () since if it is a generic of no
               ;; arguments then it will always stay so, otherwise, the first
               ;; call will have the real arguments anyway
               (one-step primaries '() '() '())]
              [else (one-around-step arounds '() '() '())])))))

(define (make-generic-combination
          #:init [init '()] #:combine [combine cons]
	  #:process-methods [process-methods #f] 
	  #:process-result [process-result #f]
	  #:control [control #f])
  (lambda (generic)
    (lambda (tail kws kw-args dummy-args)
      (let ([tail (if process-methods (process-methods tail) tail)])
        (make-keyword-procedure-0
         (lambda (kws kw-args . args)
           (let loop ([res init] [tail tail])
             ;; see *no-next-method* trick above
             (let ([*no-next-method*
                    (make-keyword-procedure-0
                     (lambda (kws kw-args . args)
                       (apply no-next-method generic (caar tail)
                              kws kw-args args)))])
               (if (null? tail)
                   (if process-result (process-result res) res)
                   (if control
                       (control loop res
                                (lambda ()
                                  (keyword-apply (cdar tail) kws kw-args
                                                 *no-next-method* args))
                                (cdr tail))
                       (loop (combine
                              (keyword-apply (cdar tail) kws kw-args
                                             *no-next-method* args) res)
                             (cdr tail))))))))))))


(define generic-+-combination
  (make-generic-combination #:init 0 #:combine +))
(define generic-list-combination
  (make-generic-combination #:process-result reverse))
(define generic-min-combination
  (make-generic-combination #:process-result (lambda (r) (apply min r))))
(define generic-max-combination
  (make-generic-combination #:process-result (lambda (r) (apply max r))))
(define generic-append-combination
  (make-generic-combination
   #:process-result (lambda (r) (apply append (reverse r)))))
(define generic-append!-combination
  (make-generic-combination
   #:process-result (lambda (r) (apply append (reverse r)))))
(define generic-begin-combination
  (make-generic-combination #:init #f #:combine (lambda (x y) x)))
(define generic-and-combination
  (make-generic-combination
   #:init #t
   #:control (lambda (loop val this tail) (and val (loop (this) tail)))))
(define generic-or-combination
  (make-generic-combination
   #:init #f
   #:control (lambda (loop val this tail) (or (this) (loop #f tail)))))


;; optimized helper
(define-syntax-rule (%struct->class c)
  (if (struct-type? c) 
      (struct-type->class c)
      c))

(define (subclass? c1 c2)
  (if (%singleton? c1)
    (if (%singleton? c2)
      (eq? (singleton-value c1) (singleton-value c2))
      (instance-of? (singleton-value c1) (%struct->class c2)))
    (memq (%struct->class c2) (%class-cpl (%struct->class c1)))))

(define (instance-of? x c)
  ;; efficiency: many cases use <top> (all untyped arguments)
  (or (eq? c <top>)
      (if (%singleton? c)
        ;; efficiency: similar to `subclass?' above
        (eq? (singleton-value c) x)
        ;;; TODO: Why do we need %struct->class here?  Should class-of
        ;;; not always return a "real" class?
        (memq (%struct->class c) (%class-cpl (%struct->class (class-of x)))))))

(define/macro class? %class? (x)
  (instance-of? x <class>))

(define (specializer? x) (or (class? x) (%singleton? x) (struct-type? x)))

(define (more-specific? c1 c2 arg)
  (if (%singleton? c1)
    (and (eq? (singleton-value c1) arg)
         (not (and (%singleton? c2) (eq? (singleton-value c1) arg))))
    (let ([cc1 (memq (%struct->class c1) (%class-cpl (class-of arg)))])
      (and cc1 (memq (%struct->class c2) (cdr cc1))))))

(add-method initialize
  (make-method #:name "{initialize <top>}"
    (list <top>)
    (procedure-reduce-keyword-arity
     (make-keyword-procedure
      (lambda (kws kw-args call-next-method object)
        ;; (printf "initialize: <top>\n")
        (error 'initialize "can't initialize an instance of ~e"
               (class-of object))))
     2 '() #f)))

(add-method initialize
  (make-method #:name "{initialize <object>}"
    (list <object>)
    (procedure-reduce-keyword-arity
     (make-keyword-procedure
      (lambda (kws kw-args call-next-method object)
        ;; (printf "initialize: <object>\n")
        (let* ([class (class-of object)]
               [field-initializers (%class-field-initializers class)])
          ;; TODO: Define the initializers so that they can be
          ;; keyword-applied.
          (for-each (lambda (init) (keyword-apply kws kw-args init '()))
                    (%class-initializers class))
          (let loop ([n 0] [inits field-initializers])
            (when (pair? inits)
              (%instance-set! object n (keyword-apply (car inits) kws kw-args '()))
              (loop (+ n 1) (cdr inits)))))))
     2 '() #f)))

(add-method initialize
  (make-method  #:name "{initialize <class>}"
    (list <class>)
    (lambda (call-next-method class
			      #:name [name '-anonymous-]
			      #:direct-supers [supers '()]
			      #:autoinitargs [autoinitargs #f]
			      #:direct-slots [dslots '()]
                              #:valid-initargs [valid-initargs '()])
      ;; (printf "initialize: <class>\n")
      (call-next-method)
      (%set-class-direct-supers!
       class
       (let ([default (*default-object-class*)])
         ;; check valid supers, and always have an object class
         (cond
          [(not default) supers] ; check disabled
          [(or (not supers) (null? supers)) (list default)]
          [(not (list? supers)) (error 'class "bad superclasses: ~e" supers)]
          [else (let ([c (find
                          (lambda (c)
                            ;; TODO: should we use <object> here
                            ;; instead of default?  We might want to
                            ;; set a specialized default class but
                            ;; still be able to inherit from
                            ;; <object>. --tc
                            (not (and (%class? c) (subclass? c default))))
                          supers)])
                  (if c
                    (error 'class "cannot inherit from a ~a, ~e"
                           (if (%class? c) "non-object class" "non-class") c)
                    supers))])))
      (%set-class-direct-slots!
       class
       (map (lambda (s)
	      (cond [(slot? s)
                     s]
                    [(pair? s)
                     (slot (first s) (initargs->hash (rest s)))]
                    [(symbol? s)
                     (make-slot-named s)]
                    [else
                     (error 'initialize
                            (format "~a is not a valid slot spec" s))]))
	    dslots))
      (%set-class-cpl!   class (compute-cpl   class))
      (%set-class-slots! class (compute-slots class))
      (%set-class-name!  class name)
      (define nfields 0)
      (define field-initializers '())
      ;; allocator: give me an initializer function, get a slot number
      (define allocator
        (lambda (init)
          (let ([f nfields])
            (set! nfields (+ nfields 1))
            (set! field-initializers
                  (cons init field-initializers))
            f)))
      (define getters-n-setters
        (map (lambda (slot)
               (cons (slot-name slot)
                     (compute-getter-and-setter class slot allocator)))
             (%class-slots class)))
      (%set-class-nfields! class nfields)
      (%set-class-field-initializers! class (reverse field-initializers))
      (%set-class-getters-n-setters! class getters-n-setters)
      (%set-class-initializers!
       class (reverse
              (append-map
               (lambda (c)
                 (if (instance-of? c <class>) (%class-initializers c) '()))
               (rest (%class-cpl class)))))
      (for ([slot (in-list (%class-slots class))])
        (set! valid-initargs
              (append (slot-valid-initargs slot) valid-initargs)))
      (%set-class-valid-initargs! ; for sanity checks
       class valid-initargs))))


(add-method initialize
  (make-method #:name "{initialize <generic>}"
    (list <generic>)
    (lambda (#:arity [arity #f] #:name [name '-anonymous-]
             #:combination [combination #f]
             call-next-method generic)
      ;; (printf "initialize <generic> ~a\n" name)
      (call-next-method)
      (%set-generic-methods! generic '())
      (%set-generic-arity!   generic arity)
      (%set-generic-name!    generic name)
      (%set-generic-combination! generic combination)
      (set-instance-proc!    generic
			     (make-keyword-procedure-0
			      (lambda (kws ks-args . args)
				(raise* make-exn:fail:contract
					"~s: no methods added yet"
					(%generic-name generic))))))))

(add-method initialize
  (make-method #:name "{initialize <generic>}"
    (list <method>)
    (lambda (#:specializers [specializers '()]
             #:procedure procedure
             #:qualifier [qualifier 'primary]
             #:name [name '-anonymous-]
             call-next-method method)
      (call-next-method)
      (%set-method-specializers! method
                                 (map (lambda (c) (%struct->class c))
                                      '() #; (getarg initargs #:specializers)
				      ))
      (%set-method-procedure!    method procedure)
      (%set-method-qualifier!    method qualifier)
      (%set-method-name!         method name)
      (set-instance-proc!        method (compute-apply-method method)))))


(add-method allocate-instance
  (make-method (list <class>)
    (lambda (call-next-method class)
      (%allocate-instance class (length (%class-field-initializers class))))))

(add-method allocate-instance
  (make-method (list <entity-class>)
    (lambda (call-next-method class)
      (%allocate-entity class (length (%class-field-initializers class))))))

(add-method compute-cpl
  (make-method (list <class>)
    (lambda (call-next-method class)
      (compute-std-cpl class %class-direct-supers))))

(add-method compute-slots
  (make-method (list <class>)
    (lambda (call-next-method class)
      ;; TODO: Check that this simplified implementation is still correct.
      
      ;; Sort the slots by order of appearance in cpl, makes them stay in the
      ;; same index, allowing optimizations for single-inheritance
      (define all-slots (append-map %class-direct-slots
                                    (reverse (%class-cpl class))))
      (let collect ([to-process all-slots]
                    [result '()])
        (if (null? to-process)
            (reverse result)
            (let*-values ([(name) (slot-name (first to-process))]
                          [(current-slots remaining-to-process)
                           (partition (lambda (s) (eq? (slot-name s) name))
                                      to-process)])
              (collect remaining-to-process
                       (cons (merge-slots current-slots)
                             result))))))))

(define-placeholders  <primitive-class> <primitive-procedure>
  <opaque-struct> <struct>)
#||
(add-method compute-getter-and-setter
  (make-method (list <class>)
    (letrec ([nothing "nothing"]
             [l-getarg
              ;; apply getarg on a list of names until get a value
              (lambda (args initargs)
                ;; give priority to first initargs
                (if (null? initargs)
                  nothing
                  (let ([x #f #;(getarg args (car initargs) nothing)
			   ])
                    (if (eq? x nothing) (l-getarg args (cdr initargs)) x))))])
      (lambda (call-next-method class slot allocator)
        (let ([initargs    #f #;(getargs (cdr slot) #:initarg)
			   ]
              [initializer #f #;(getarg (cdr slot) #:initializer)]
              [initvalue   #f #;(getarg (cdr slot) #:initvalue ???)]
              [type        #f #;(getarg (cdr slot) #:type #f)]
              [allocation  #f #;(getarg (cdr slot) #:allocation #:instance)]
              [lock        #f #;(getarg (cdr slot) :lock #f)])
          (define init
            (if initializer
              (if (eq? 0 (procedure-arity initializer))
                (lambda args (initializer)) initializer)
              (lambda args initvalue)))
          (define (init-slot . args)
            (let ([result (l-getarg args initargs)])
              (when (eq? result nothing)
		;;; TODO: keyword-apply?
                (set! result (apply init args)))
              (when (and type (not (eq? result ???))
                         (not (instance-of? result type)))
                (error 'class
                       "bad initial value type for slot ~e in ~e (~e not a ~e)"
                       (car slot) class result type))
              result))
          (when (and type (not (specializer? type)))
            (error 'class "bad type specifier for ~e: ~e" (car slot) type))
          (case allocation
            [(#:instance)
             (let* ([f (allocator init-slot)]
                    [g+s (mcons (lambda (o) (%instance-ref o f))
                                (if (and type (not (eq? <top> type)))
                                  (lambda (o n)
                                    (if (instance-of? n type)
                                      (%instance-set! o f n)
                                      (raise* make-exn:fail:contract
                                              "slot-set!: wrong type for slot ~
                                               `~.s' in ~e (~e not in ~e)"
                                              (car slot) class n type)))
                                  (lambda (o n) (%instance-set! o f n))))])
               (when lock
                 (lock-setter! g+s lock
			       (lambda ()
				 (raise* make-exn:fail:contract
					 "slot-set!: slot `~.s' in ~.s is locked"
					 (car slot) (%class-name class)))))
               g+s)]
            [(#:class)
             (unless (null? initargs)
               (let ([setter #f])
                 (%set-class-initializers!
                  class
                  (cons (lambda args
                          (let ([result (l-getarg args initargs)])
                            ;; cache the setter
                            (unless setter
                              (set! setter
                                    (mcdr (cdr (assq (car slot)
                                                     (%class-getters-n-setters
                                                      class))))))
                            (unless (eq? result nothing)
                              (setter #f result))))
                        (%class-initializers class)))))
             (if (and (assq (car slot) (%class-direct-slots class))
                      #;
		      (getarg (cdr (assq (car slot)
                                         (%class-direct-slots class)))
                              #:allocation #f))
               ;; the slot was declared as #:class here
               (let* ([cell (init)] ; default value - no arguments
                      [g+s (mcons (lambda (o) cell)
                                  (lambda (o n)
                                    (if (and type (not (instance-of? n type)))
                                      (raise*
                                       make-exn:fail:contract
                                       "slot-set!: wrong type for shared slot ~
                                        `~.s' in ~e (~e not in ~e)"
                                       (car slot) class n type)
                                      (set! cell n))))])
                 (when lock
                   (lock-setter! (car slot) g+s lock
				 (lambda ()
				   (raise* make-exn:fail:contract
					   "slot-set!: slot `~.s' in ~.s is locked"
					   (car slot) (%class-name class)))))
                 g+s)
               ;; the slot was inherited as #:class - fetch its getters/setters
               (let loop ([cpl (cdr (%class-cpl class))])
                 (cond [(assq (car slot) (%class-getters-n-setters (car cpl)))
                        => cdr]
                       [else (loop (cdr cpl))])))]
            [else
             (error 'class
                    "allocation for `~.s' must be #:class or #:instance, got ~e"
                    (car slot) allocation)]))))))

;;; Use the previous function when populating this generic.
(add-method compute-apply-method
  (make-method (list <method>) method:compute-apply-method))

(add-method no-next-method
  (make-method (list <generic> <method>)
    (lambda (call-next-method generic method kws kw-args . args)
      (raise* make-exn:fail:contract
              (string-append
	       "~s: no applicable next method to call"
	       (case (%method-qualifier method)
		 [(#:before) " in a `before' method"]
		 [(#:after)  " in an `after' method"]
		 [else ""])
	       " with arguments: ~e"
	       (if (null? kws)
		   ""
		   (format " and keywords: ~e"
			   (append-map list kws kw-args))))
              (%generic-name generic) args))))

(add-method no-next-method
  (make-method (list (singleton #f) <method>)
    (lambda (call-next-method generic method kws kw-args . args)
      (raise* make-exn:fail:contract
              (string-append
	       "~s: no applicable next method in a direct method call"
	       " with arguments: ~e"
	       (if (null? kws)
		   ""
		   (format " and keywords: ~e"
			   (append-map list kws kw-args))))
              (%method-name method) args))))

(add-method no-applicable-method
  (make-method (list <generic>)
    (lambda (call-next-method generic . args)
      (raise* make-exn:fail:contract
              "~s: no applicable primary methods for arguments ~e, of types ~e"
              (%generic-name generic) args (map class-of args)))))


;;; ---------------------------------------------------------------------------
;;; Customization variables

(define *make-safely* (make-parameter #f))

(define (check-initargs class initargs)
  ;; sanity check - verify sensible keywords given
  (let ([valid-initargs (%class-valid-initargs class)])
    (or (not valid-initargs)
        (let loop ([args initargs])
          (cond [(null? args) #t]
                [(not (and (pair? args) (pair? (cdr args))))
                 (error 'make "error in initargs for ~e; arg list not balanced"
                        class)]
                [(not (symbol? (car args)))
                 (error 'make "error in initargs for ~e; ~e is not a keyword"
                        class (car args))]
                [(not (memq (car args) valid-initargs))
                 (error 'make "error in initargs for ~e; unknown keyword: ~e"
                        class (car args))]
                [else (loop (cddr args))])))))

;;; ---------------------------------------------------------------------------
;;; Make `make' a generic function

;;; Now everything works, both generic functions and classes, so we can turn on
;;; the real MAKE.
;;; ELI: This is turned into a generic function - do this carefully - first
;;; create the generic function and the method instances, then change make.

(let ([m (make-method (list <class>)
           (procedure-reduce-keyword-arity
            (make-keyword-procedure
             (lambda (kws kw-args call-next-method class)
               (let ([instance (keyword-apply allocate-instance kws kw-args class)])
                 ;; FIXME
                 #;(when (*make-safely*) (check-initargs class initargs))
                 (keyword-apply kws kw-args initialize instance)
                 instance)))
            2 '() #f))]
      [g (make-generic-function 'make)])
  (add-method g m)
  (set! make g))

;; The clean concept behind this is due to Joe Marshall.

(provide rec-make)
(define-syntax-rule (rec-make (name class arg ...) ...)
  (let ([name (allocate-instance class (list arg ...))] ...)
    (when (*make-safely*) (check-initargs class (list arg ...)) ...)
    (initialize name (list arg ...)) ...
    (values name ...)))

;;; ---------------------------------------------------------------------------
;;; Make `add-method' a generic function

;;; Use this to compute a name for the method.  specs is a list of classes or
;;; class-names (in case of unnamed-methods in clos.rkt).
(define (compute-method-name specs generic-name)
  (define (spec-string spec)
    (cond [(%singleton? spec) (format "{~.s}" (singleton-value spec))]
          [(%class? spec)     (symbol->string
                               (%class-name (%struct->class spec)))]
          [else               "???"]))
  (string->symbol
   (apply string-append
          (symbol->string generic-name) ":"
          (if (null? specs)
            '("()")
            (cons (spec-string (car specs))
                  (map (lambda (c) (string-append "," (spec-string c)))
                       (cdr specs)))))))

(let ([old-add-method add-method])
  (set! add-method (make <generic> #:name 'add-method #:arity 2))
  (old-add-method add-method
    (make-method (list <generic> <method>)
      (lambda (call-next-method generic method)
        (let ([method-arity (method-arity method)]
              [generic-arity (%generic-arity generic)])
          (cond
           [(not generic-arity)
            (%set-generic-arity! generic method-arity)]
           ;; note: equal? works on arity-at-least structs
           [(not (equal? generic-arity method-arity))
            (error 'add-method
                   "wrong arity for `~.s', expects ~a; given a method with ~a"
                   (%generic-name generic)
                   (if (integer? generic-arity)
                     generic-arity
                     (format "at-least-~a"
                             (arity-at-least-value generic-arity)))
                   (if (integer? method-arity)
                     method-arity
                     (format "at-least-~a"
                             (arity-at-least-value method-arity))))])
          ;; set a name for the method if none (when attached to a generic)
          (let ([n (%method-name method)])
            (unless (and n (not (eq? n '-anonymous-)))
              (%set-method-name!
               method
               (let* ([psym (object-name (%method-procedure method))]
                      [pstr (and psym (symbol->string psym))])
                 (if (or (not pstr) (regexp-match? #rx":[0-9]*:[0-9]*$" pstr))
                   (compute-method-name (%method-specializers method)
                                        (%generic-name generic))
                   psym)))))
          (old-add-method generic method))))))

;;; Optimized frequently used accessors:
;;; This is possible because of the ordering of the slots in compute-slots,
;;; works only for single-inheritance.  Note that there is no type checking -
;;; it is unsafe, but makes things around 5-6 times faster!
(set! %class-direct-slots        (%slot-getter <class>   'direct-slots))
(set! %class-direct-supers       (%slot-getter <class>   'direct-supers))
(set! %class-slots               (%slot-getter <class>   'slots))
(set! %class-nfields             (%slot-getter <class>   'nfields))
(set! %class-field-initializers  (%slot-getter <class>   'field-initializers))
(set! %class-getters-n-setters   (%slot-getter <class>   'getters-n-setters))
(set! %class-cpl                 (%slot-getter <class>   'cpl))
(set! %class-name                (%slot-getter <class>   'name))
(set! %class-initializers        (%slot-getter <class>   'initializers))
(set! %class-valid-initargs      (%slot-getter <class>   'valid-initargs))
(set! %generic-methods           (%slot-getter <generic> 'methods))
(set! %generic-arity             (%slot-getter <generic> 'arity))
(set! %generic-name              (%slot-getter <generic> 'name))
(set! %generic-combination       (%slot-getter <generic> 'combination))
(set! %method-specializers       (%slot-getter <method>  'specializers))
(set! %method-procedure          (%slot-getter <method>  'procedure))
(set! %method-qualifier          (%slot-getter <method>  'qualifier))
(set! %method-name               (%slot-getter <method>  'name))
(set! %set-class-direct-slots!   (%slot-setter <class>   'direct-slots))
(set! %set-class-direct-supers!  (%slot-setter <class>   'direct-supers))
(set! %set-class-slots!          (%slot-setter <class>   'slots))
(set! %set-class-nfields!        (%slot-setter <class>   'nfields))
(set! %set-class-field-initializers!(%slot-setter <class> 'field-initializers))
(set! %set-class-getters-n-setters! (%slot-setter <class> 'getters-n-setters))
(set! %set-class-cpl!            (%slot-setter <class>   'cpl))
(set! %set-class-name!           (%slot-setter <class>   'name))
(set! %set-class-initializers!   (%slot-setter <class>   'initializers))
(set! %set-class-valid-initargs! (%slot-setter <class>   'valid-initargs))
(set! %set-generic-methods!      (%slot-setter <generic> 'methods))
(set! %set-generic-arity!        (%slot-setter <generic> 'arity))
(set! %set-generic-name!         (%slot-setter <generic> 'name))
(set! %set-generic-combination!  (%slot-setter <generic> 'combination))
(set! %set-method-specializers!  (%slot-setter <method>  'specializers))
(set! %set-method-procedure!     (%slot-setter <method>  'procedure))
(set! %set-method-qualifier!     (%slot-setter <method>  'qualifier))
(set! %set-method-name!          (%slot-setter <method>  'name))
;; Optimize these internal ones as well.
(set! %generic-app-cache         (%slot-getter <generic> 'app-cache))
(set! %generic-singletons-list   (%slot-getter <generic> 'singletons-list))
(set! %set-generic-app-cache!    (%slot-setter <generic> 'app-cache))
(set! %set-generic-singletons-list! (%slot-setter <generic> 'singletons-list))

;;; ---------------------------------------------------------------------------
;;; Built-in classes.

(define <primitive-class>
  (make <class> #:direct-supers (list <class>)
                #:direct-slots  '()
                #:name          '<primitive-class>
                ;; needed so structs can turn to classes even if *make-safely*
                #:valid-initargs #f))
;; Normally, can't allocate these.
(add-method allocate-instance
  (make-method (list <primitive-class>)
    (lambda (call-next-method class initargs)
      (error 'allocate-instance "can't instantiate a primitive class ~e"
             class))))

(define <builtin>
  (make <class> #:direct-supers (list <top>)
                #:direct-slots  '()
                #:name          '<builtin>))

(define-syntax defprimclass
  (syntax-rules ()
    [(_ primclass)
     (defprimclass primclass <builtin>)]
    [(_ primclass supers ...)
     (define primclass
       (make <primitive-class>
	 #:name          'primclass
	 #:direct-supers (list supers ...)
	 #:direct-slots  '()))]))

(defprimclass <sequence>)
(defprimclass <mutable>)
(defprimclass <immutable>)
(defprimclass <pair> <sequence>)
(defprimclass <mutable-pair> <pair> <mutable>)
(define <mpair> <mutable-pair>) ; alias
(defprimclass <immutable-pair> <pair> <immutable>)
(defprimclass <list> <sequence>)
(defprimclass <nonempty-list> <pair> <list> <immutable>)
(defprimclass <null> <list>)
(defprimclass <vector> <sequence> <mutable>)
(defprimclass <char>)
(defprimclass <string-like> <sequence>)
(defprimclass <mutable-string-like> <string-like> <mutable>)
(defprimclass <immutable-string-like> <string-like> <immutable>)
(defprimclass <string> <string-like>)
(defprimclass <mutable-string> <string> <mutable-string-like>)
(defprimclass <immutable-string> <string> <immutable-string-like>)
(defprimclass <bytes> <string-like>)
(defprimclass <mutable-bytes> <bytes> <mutable-string-like>)
(defprimclass <immutable-bytes> <bytes> <immutable-string-like>)
(defprimclass <path> <immutable-string-like>)
(defprimclass <symbol>)
(defprimclass <keyword> <symbol>)
(defprimclass <real-keyword>)
(defprimclass <boolean>)
;; Have all possible number combinations in any case
(defprimclass <number>)
(defprimclass <exact> <number>)
(defprimclass <inexact> <number>)
(defprimclass <complex> <number>)
(defprimclass <real> <complex>)
(defprimclass <rational> <real>)
(defprimclass <integer> <rational>)
(defprimclass <exact-complex> <complex> <exact>)
(defprimclass <inexact-complex> <complex> <inexact>)
(defprimclass <exact-real> <real> <exact-complex>)
(defprimclass <inexact-real> <real> <inexact-complex>)
(defprimclass <exact-rational> <rational> <exact-real>)
(defprimclass <inexact-rational> <rational> <inexact-real>)
(defprimclass <exact-integer> <integer> <exact-rational>)
(defprimclass <inexact-integer> <integer> <inexact-rational>)
(defprimclass <end-of-file>)
(defprimclass <port>)
(defprimclass <input-port> <port>)
(defprimclass <output-port> <port>)
(defprimclass <stream-port> <port>)
;; Racket stuff
(defprimclass <input-stream-port> <input-port> <stream-port>)
(defprimclass <output-stream-port> <output-port> <stream-port>)
(defprimclass <void>)
(defprimclass <box> <mutable>)
(defprimclass <weak-box> <box>)
(defprimclass <regexp>)
(defprimclass <byte-regexp>)
(defprimclass <parameter>)
(defprimclass <promise>)
(defprimclass <exn>)
(defprimclass <exn:fail>  <exn>)
(defprimclass <exn:break> <exn>)
;; make these classes used when we see exn structs
(let ([set-exn-class
       (lambda (class make-exn . xs)
         (hash-set! struct-to-class-table
                          (let-values ([(e _)
                                        (struct-info
                                         (apply make-exn "foo"
                                                (current-continuation-marks)
                                                xs))])
                            e)
                          class))])
  (set-exn-class <exn> make-exn)
  (set-exn-class <exn:fail> make-exn:fail)
  (set-exn-class <exn:break> make-exn:break (let/ec e e)))
(defprimclass <semaphore>)
(defprimclass <hash-table>)
(defprimclass <subprocess>)
(defprimclass <thread>)
(defprimclass <syntax>)
(defprimclass <identifier-syntax> <syntax>)
(defprimclass <namespace>)
(defprimclass <custodian>)
(defprimclass <tcp-listener>)
(defprimclass <security-guard>)
(defprimclass <will-executor>)
(defprimclass <struct-type>)
(defprimclass <inspector>)
(defprimclass <pseudo-random-generator>)
(defprimclass <compiled-expression>)
(defprimclass <unknown-primitive>)
(defprimclass <struct>)
(defprimclass <opaque-struct> <struct>)

(define <procedure>
  (make <procedure-class> #:name          '<procedure>
                          #:direct-supers (list <builtin> <function>)
                          #:direct-slots  '()))

(define <primitive-procedure>
  (make <procedure-class>
        #:name          '<primitive-procedure>
        #:direct-supers (list <procedure>)
        #:direct-slots  '()))

(*default-object-class* <object>) ; turn auto-superclass back on

(set! class-of
      (lambda (x)
        ;; If all Schemes were IEEE compliant, the order of these wouldn't
        ;; matter?
        ;; ELI: changed the order so it fits better the expected results.
        (cond [(instance?    x) (instance-class x)]
              [(struct? x)
               (let-values ([(type _) (struct-info x)])
                 (if type (struct-type->class type) <opaque-struct>))]
              [(procedure?   x) (cond [(parameter? x) <parameter>]
                                      [(primitive? x) <primitive-procedure>]
                                      [else <procedure>])]
              [(string?      x) (if (immutable? x) <immutable-string> <string>)]
              [(pair?        x) (if (list? x) <nonempty-list> <immutable-pair>)]
              [(null?        x) <null>]
              [(symbol?      x) (if (keyword? x) <keyword> <symbol>)]
              [(number?      x)
               (if (exact? x)
                 (cond [(integer?  x) <exact-integer>]
                       [(rational? x) <exact-rational>]
                       [(real?     x) <exact-real>]
                       [(complex?  x) <exact-complex>]
                       [else <exact>]) ; should not happen
                 (cond [(integer?  x) <inexact-integer>]
                       [(rational? x) <inexact-rational>]
                       [(real?     x) <inexact-real>]
                       [(complex?  x) <inexact-complex>]
                       [else <inexact>]))] ; should not happen
              [(boolean?     x) <boolean>]
              [(char?        x) <char>]
              [(bytes?       x) (if (immutable? x) <immutable-bytes> <bytes>)]
              [(path?        x) <path>]
              [(vector?      x) <vector>]
              [(mpair?       x) <mutable-pair>]
              [(eof-object?  x) <end-of-file>]
              [(input-port?  x)
               (if (file-stream-port? x) <input-stream-port> <input-port>)]
              [(output-port? x)
               (if (file-stream-port? x) <output-stream-port> <output-port>)]
              [(void?           x) <void>]
              [(box?            x) <box>]
              [(weak-box?       x) <weak-box>]
              [(regexp?         x) <regexp>]
              [(byte-regexp?    x) <byte-regexp>]
              [(promise?        x) <promise>]
              [(keyword?        x) <keyword>]
              [(semaphore?      x) <semaphore>]
              [(hash?           x) <hash-table>]
              [(thread?         x) <thread>]
              [(subprocess?     x) <subprocess>]
              [(syntax?         x)
               (if (identifier? x) <identifier-syntax> <syntax>)]
              [(namespace?      x) <namespace>]
              [(custodian?      x) <custodian>]
              [(tcp-listener?   x) <tcp-listener>]
              [(security-guard? x) <security-guard>]
              [(will-executor?  x) <will-executor>]
              [(struct-type?    x) <struct-type>]
              [(inspector?      x) <inspector>]
              [(pseudo-random-generator? x) <pseudo-random-generator>]
              [(compiled-expression? x) <compiled-expression>]
              [else <unknown-primitive>])))

;;; Some useful predicates.

(define (builtin?  x) (instance-of? x <builtin>))
(define (function? x) (instance-of? x <function>))
(define (generic?  x) (instance-of? x <generic>))
(define (method?   x) (instance-of? x <method>))

||#
;;; Add some additional indentation information for emacs
#||
Local Variables:
eval: (mapc (lambda (sym)
              (put sym 'scheme-indent-function #'scheme-let-indent))
            (list 'let-args))
End:
||#
