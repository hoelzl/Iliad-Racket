#lang racket

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
;;;   (MAKE-CLASS list-of-superclasses list-of-slot-names)
;;;   (MAKE-GENERIC-FUNCTION)
;;;   (MAKE-METHOD list-of-specializers procedure)
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
;;;   (define <position> (make-class (list <object>) (list 'x 'y)))
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

#||
;; A simple topological sort.
;; It's in this file so that both TinyClos and Objects can use it.
;; This is a fairly modified version of code I originally got from Anurag
;; Mendhekar <anurag@moose.cs.indiana.edu>.
(define (compute-std-cpl c get-direct-supers)
  (top-sort (build-transitive-closure get-direct-supers c)
            (build-constraints get-direct-supers c)
            (std-tie-breaker get-direct-supers)))
(define (top-sort elements constraints tie-breaker)
  (let loop ([elements elements] [constraints constraints] [result '()])
    (if (null? elements)
      result
      (let ([can-go-in-now
             (filter (lambda (x)
                       (every (lambda (constraint)
                                (or (not (eq? (cadr constraint) x))
                                    (memq (car constraint) result)))
                              constraints))
                     elements)])
        (if (null? can-go-in-now)
          (error 'top-sort "invalid constraints")
          (let ([choice (if (null? (cdr can-go-in-now))
                          (car can-go-in-now)
                          (tie-breaker result can-go-in-now))])
            (loop (filter (lambda (x) (not (eq? x choice))) elements)
                  constraints (append result (list choice)))))))))
(define (std-tie-breaker get-supers)
  (lambda (partial-cpl min-elts)
    (let loop ([pcpl (reverse partial-cpl)])
      (let* ([current-elt (car pcpl)]
             [ds-of-ce (get-supers current-elt)]
             [common (filter (lambda (x) (memq x ds-of-ce)) min-elts)])
        (if (null? common)
          (if (null? (cdr pcpl))
            (error 'std-tie-breaker "nothing valid") (loop (cdr pcpl)))
          (car common))))))
(define (build-transitive-closure get-follow-ons x)
  (let track ([result '()] [pending (list x)])
    (if (null? pending)
      result
      (let ([next (car pending)])
        (if (memq next result)
          (track result (cdr pending))
          (track (cons next result)
                 (append (get-follow-ons next) (cdr pending))))))))
(define (build-constraints get-follow-ons x)
  (let loop ([elements (build-transitive-closure get-follow-ons x)]
             [this-one '()]
             [result '()])
    (if (or (null? this-one) (null? (cdr this-one)))
      (if (null? elements)
        result
        (loop (cdr elements)
              (cons (car elements) (get-follow-ons (car elements)))
              result))
      (loop elements
            (cdr this-one)
            (cons (list (car this-one) (cadr this-one)) result)))))

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
(define unspecified-initializer (lambda args ???))
(define false-func (lambda args #f))

;; Basic allocation follows, all was in a single let, but this is not needed
;; with Racket's modules.  Also modified to use simple structs for
;; everything, including entities since PLT has applicable struct objects.

(define-values (struct:instance make-instance instance? inst-ref inst-set!)
  ;; slots: applicable, class, function, slots-vector
  (make-struct-type 'swindleobj #f 3 0 #f '() (current-inspector)
                    (lambda (o . args) (apply (instance-proc o) args))))
(defsubst (instance-class x) (inst-ref x 0))
(defsubst (instance-proc  x) (inst-ref x 1))
(defsubst (instance-slots x) (inst-ref x 2))
(defsubst (set-instance-class! x c) (inst-set! x 0 c))
(defsubst (set-instance-proc!  x p) (inst-set! x 1 p))
(defsubst (set-instance-slots! x s) (inst-set! x 2 s))

(defsubst (%instance-ref o f)    (vector-ref (instance-slots o) f))
(defsubst (%instance-set! o f n) (vector-set! (instance-slots o) f n))

(define (%allocate-instance class nfields)
  (make-instance class
                 (lambda args
                   (error 'instance
                          "an instance isn't a procedure -- can't apply it"))
                 (make-vector nfields ???)))

(define (%allocate-entity class nfields)
  (letrec ([o (make-instance
               class
               (lambda args
                 (error 'entity
                        "tried to call an entity before its proc is set"))
               (make-vector nfields ???))])
    o))

;; This is used only once as part of bootstrapping the braid.
(define (set-instance-class-to-self! class)
  (set-instance-class! class class))

(define (change-class! obj new-class . initargs)
  (let ([new (apply make new-class initargs)]
        [new-slots (%class-slots new-class)])
    (dolist [slot (%class-slots (class-of obj))]
	    ;;; FIXME
	    (when (and #;(not (eq? #:class (getarg (cdr slot) #:allocation #:instance)))
		       (assq (car slot) new-slots))
	      (slot-set! new (car slot) (slot-ref obj (car slot)))))
    (set-instance-slots! obj (instance-slots new))
    (set-instance-class! obj new-class)))

;; This might be cute for some ugly hacks but not needed for now.
;; Copies the contents of source to target, making it an "alias" object.  This
;; is no re-provided by clos.rkt, but maybe it will in the future...
;; (define (copy-object-contents! target source)
;;   (set-instance-class! target (instance-class source))
;;   (set-instance-proc!  target (instance-proc  source))
;;   (set-instance-slots! target (instance-slots source)))

(provide set-instance-proc!) ; dangerous!

;; Basic allocation ends here.

(provide instance?)
(define object? instance?)

(define (class-of x)
  ;; This is an early version that will be modified when built-in types are
  ;; introduced later.
  (if (instance? x) (instance-class x) <top>))

;;; Now we can get down to business.  First, we initialize the braid.
;;; For Bootstrapping, we define an early version of MAKE.  It will be changed
;;; to the real version later on.
(define (make class 
	  #:direct-supers [dsupers '()]
	  #:direct-slots [direct-slots '()]
	  #:name [name '-anonymous-]
	  #:arity [arity #f]
	  #:specializers [specializers '()]
	  #:procedure [procedure #f]
	  #:qualifier [qualifier 'primary])
  (cond [(or (eq? class <class>) (eq? class <entity-class>))
         (let* ([new     (%allocate-instance class
                                             (length the-slots-of-a-class))]
                [dslots  (map list direct-slots)]
                [cpl     (let loop ([sups dsupers] [so-far (list new)])
                           (if (null? sups)
                             (reverse so-far)
                             (loop (append (cdr sups)
                                           (%class-direct-supers (car sups)))
                                   (if (memq (car sups) so-far)
                                     so-far
                                     (cons (car sups) so-far)))))]
                [slots
                 (apply append dslots (map %class-direct-slots (cdr cpl)))]
                [nfields 0]
                [field-initializers '()]
                ;; this is a temporary allocator version, kept as the original
                ;; one in tiny-clos.  the permanent version below is modified.
                [allocator
                 (lambda (init)
                   (let ([f nfields])
                     (set! nfields (+ nfields 1))
                     (set! field-initializers (cons init field-initializers))
                     (mcons (lambda (o)   (%instance-ref  o f))
                            (lambda (o n) (%instance-set! o f n)))))]
                [getters-n-setters
                 (map (lambda (s)
                        (cons (car s) (allocator unspecified-initializer)))
                      slots)])
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
           new)]
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

(define (slot-ref object slot-name)
  ((lookup-slot-info (class-of object) slot-name mcar) object))
(defsubst (%slot-ref object slot-name)
  ((lookup-slot-info (class-of object) slot-name mcar) object))

(define (slot-set! object slot-name new-value)
  ((lookup-slot-info (class-of object) slot-name mcdr) object new-value))
(defsubst (%slot-set! object slot-name new-value)
  ((lookup-slot-info (class-of object) slot-name mcdr) object new-value))

(define set-slot-ref! slot-set!)

;; This is a utility that is used to make locked slots
(define (make-setter-locked! g+s key error)
  (let ([setter (mcdr g+s)])
    (set-mcdr! g+s
      (lambda (o n)
        (cond [(and (pair? n) (eq? key (car n)) (not (eq? key #t)))
               (setter o (cdr n))]
              [(eq? ??? ((mcar g+s) o)) (setter o n)]
              [else (error)])))))

(define (slot-bound? object slot-name)
  (not (eq? ??? (%slot-ref object slot-name))))

(define (lookup-slot-info class slot-name selector)
  (selector (cdr (or (assq slot-name
                           ;; no need to ground slot-ref any more! -- see below
                           ;; (if (eq? class <class>)
                           ;;   ;;* This grounds out the slot-ref tower
                           ;;   getters-n-setters-for-class
                           ;;   (%class-getters-n-setters class))
                           (%class-getters-n-setters class))
                     (raise* make-exn:fail:contract
                             "slot-ref: no slot `~.s' in ~.s"
                             slot-name class)))))

;;; These are for optimizations - works only for single inheritance!
(define (%slot-getter class slot-name)
  (lookup-slot-info class slot-name mcar))
(define (%slot-setter class slot-name)
  (lookup-slot-info class slot-name mcdr))


;;; Singleton class.  A hash-table is used so it is still possible to compare
;;; classes with eq?.
(define singleton-classes (make-weak-hasheq))

(define (singleton x)
  (or (hash-ref singleton-classes x false-func)
      (let ([c (list 'singleton x)])
        (hash-set! singleton-classes x c)
        c)))
(define (singleton? x)
  (and (pair? x) (eq? (car x) 'singleton)))
(defsubst (%singleton? x)
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
                            '#:name name '#:direct-supers supers))])
         (hash-set! struct-to-class-table stype this)
         this)))))

(define (class-direct-slots       c) (%slot-ref c 'direct-slots))
(define (class-direct-supers      c) (%slot-ref c 'direct-supers))
(define (class-slots              c) (%slot-ref c 'slots))
(define  (class-nfields            c) (%slot-ref c 'nfields))
(define  (class-field-initializers c) (%slot-ref c 'field-initializers))
(define  (class-getters-n-setters  c) (%slot-ref c 'getters-n-setters))
(define (class-cpl                c) (%slot-ref c 'cpl))
(define (class-name               c) (%slot-ref c 'name))
(define (class-initializers       c) (%slot-ref c 'initializers))
(define  (class-valid-initargs     c) (%slot-ref c 'valid-initargs))
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
           (make-arity-at-least (sub1 (arity-at-least-value a)))]
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
    direct-slots               ; ((name . options) ...)
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
((mcdr (cdr (assq 'getters-n-setters getters-n-setters-for-class)))
 <class> getters-n-setters-for-class)
;; and now the direct `%class-getters-n-setters' version:
(set! %class-getters-n-setters
      ;; and (lookup-slot-info <class> 'getters-n-setters mcar) translates to:
      (mcar (cdr (assq 'getters-n-setters getters-n-setters-for-class))))

(define <top> (make <class>
		#:direct-supers '()
		#:direct-slots  '()
		#:name          '<top>))

(define <object> (make <class>
		   #:direct-supers (list <top>)
		   #:direct-slots  '()
		   #:name          '<object>))

;;; This cluster, together with the first cluster above that defines <class>
;;; and sets its class, have the effect of:
;;;   (define <class>
;;;     (make <class> #:direct-supers (list <object>)
;;;                   #:direct-slots  '(direct-supers ...)
;;;                   #:name          '<class>))
(%set-class-direct-supers!      <class> (list <object>))
(%set-class-cpl!                <class> (list <class> <object> <top>))
(%set-class-direct-slots!       <class> (map list the-slots-of-a-class))
(%set-class-slots!              <class> (map list the-slots-of-a-class))
(%set-class-nfields!            <class> (length the-slots-of-a-class))
(%set-class-field-initializers! <class> (map (lambda (s)
                                               unspecified-initializer)
                                             the-slots-of-a-class))
(%set-class-name!               <class> '<class>)
(%set-class-initializers!       <class> '())
(%set-class-valid-initargs!     <class> #f)

(define <procedure-class>
  (make <class>
    #:direct-supers (list <class>)
    #:direct-slots  '()
    #:name          '<procedure-class>))

(define <entity-class>
  (make <class>
    #:direct-supers (list <procedure-class>)
    #:direct-slots  '()
    #:name          '<entity-class>))

(define <function>
  (make <class>
    #:direct-supers (list <top>)
    #:direct-slots  '()
    #:name          '<function>))

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
    #:direct-slots  '(methods arity name combination
			      app-cache singletons-list) ; see above
    #:name          '<generic>))

(define <method>
  (make <entity-class>
    #:direct-supers (list <object> <function>)
    #:direct-slots  '(specializers procedure qualifier name)
    #:name          '<method>))

;; Do this since compute-apply-method relies on them not changing, as well as a
;; zillion other places.  A method should be very similar to a lambda.
(dolist [slot '(specializers procedure qualifier)]
  (make-setter-locked! (lookup-slot-info <method> slot values) #t
    (lambda ()
      (raise* make-exn:fail:contract
              "slot-set!: slot `~.s' in <method> is locked" slot))))

(define (make-class direct-supers direct-slots)
  (make <class>
    #:direct-supers direct-supers
    #:direct-slots  direct-slots))

(define (make-generic-function . name/arity)
  (cond
   [(null? name/arity) (make <generic>)]
   [(null? (cdr name/arity))
    (let ([n/a (car name/arity)])
      (if (integer? n/a)
        (make <generic> #:arity n/a) (make <generic> #:name n/a)))]
   [else (make <generic> #:name (car name/arity) #:arity (cadr name/arity))]))

(define (make-method specializers procedure)
  (make <method>
    #:specializers specializers
    #:procedure    procedure))

(define no-next-method       (make-generic-function 'no-next-method))
(define no-applicable-method (make-generic-function 'no-applicable-method))

;;; Add possibility of generic-independent method application - this is the
;;; instance-proc of methods, which is activated when you apply the object (in
;;; the original, methods could not be applied).  This is defined using this
;;; name and arguments because it is later used directly by the generic
;;; function (cannot use the generic in the initial make since methods need to
;;; be created when the generics are constructed).
(define (method:compute-apply-method call-next-method method)
  (let* ([specializers (%method-specializers method)]
         [*no-next-method* ; see the *no-next-method* trick below
          (lambda args (apply no-next-method #f method args))]
         [proc     (%method-procedure method)]
         [arity    (method-arity method)]
         [exact?   (integer? arity)]
         [required ((if exact? identity arity-at-least-value) arity)])
    (when (and exact? (> (length specializers) required))
      (error 'compute-apply-method
             "got ~e specializers for ~s - too much for procedure arity ~a"
             (length specializers) (%method-name method) required))
    (lambda args
      (cond [(if exact?
               (not (= (length args) required)) (< (length args) required))
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
            [else (apply proc *no-next-method* args)]))))

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
    (let loop ([n n] [r '()]) (if (zero? n) r (loop (sub1 n) (cons #f r)))))
  (let ([tables    (%generic-singletons-list generic)]
        [specs     (%method-specializers method)]
        [qualifier (%method-qualifier method)])
    ;; make sure that tables always contain enough hash tables (or #f's)
    (cond [(eq? tables ???)
           (set! tables (n-falses (length specs)))]
          [(< (length tables) (length specs))
           (set! tables (append
                         tables
                         (n-falses (- (length specs) (length tables)))))])
    (set! tables (add-to-singletons-list specs tables))
    (%set-generic-singletons-list! generic tables)
    (if (memq generic generic-invocation-generics)
      ;; reset all caches by changing the value of *generic-app-cache-tag*
      (set! *generic-app-cache-tag* (list #f))
      ;; reset this generic app-cache
      (%set-generic-app-cache! generic ???))
    (%set-generic-methods!
     generic
     (cons method
           (filter (lambda (m)
                     (not (and (every eq? (method-specializers m) specs)
                               (eq? (%method-qualifier m) qualifier))))
                   (%generic-methods generic))))
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

(set-instance-proc! compute-apply-generic
  (lambda (generic)
    ((%method-procedure (car (%generic-methods generic))) '() generic)))

(add-method compute-apply-generic
  (make-method (list <generic>)
    (lambda (call-next-method generic)
      #| The code below is the original, then comes the optimized version below
      ;; see the definition of the <generic> class above.
      (lambda args
        (if (and (memq generic generic-invocation-generics)    ;* Ground case
                 (memq (car args) generic-invocation-generics))
          (apply (%method-procedure (last (%generic-methods generic))) #f args)
          ((compute-apply-methods generic)
           (compute-methods generic args) . args)))
      |#
      ;; This function converts the list of arguments to a list of keys to look
      ;; for in the cache - use the argument's class except when there is a
      ;; corresponding singleton with the same value at the same position.
      (define (get-keys args tables)
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
      (lambda args
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
          (define (compute-callable)
            (let ([c (if ground?
                       (let ([m (%method-procedure
                                 (last (%generic-methods generic)))])
                         (lambda args (apply m #f args)))
                       (compute-apply-methods
                        generic (compute-methods generic args)))])
              (hash-set! (cdr app-cache) keys c)
              c))
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
          (when (or (eq? app-cache ???)
                    (not (eq? (car app-cache) *generic-app-cache-tag*)))
            (set! app-cache (cons *generic-app-cache-tag*
                                  (make-weak-hash)))
            (%set-generic-app-cache! generic app-cache))
          (apply (hash-ref (cdr app-cache) keys compute-callable)
		 args))))))

(add-method compute-methods
  (make-method (list <generic>)
    (lambda (call-next-method generic args)
      (let ([more-specific? (compute-method-more-specific? generic)])
        (sort (filter
               (lambda (m)
                 ;; Note that every only goes as far as the shortest list
                 (every instance-of? args (%method-specializers m)))
               (%generic-methods generic))
              (lambda (m1 m2) (more-specific? m1 m2 args)))))))

(add-method compute-method-more-specific?
  (make-method (list <generic>)
    (lambda (call-next-method generic)
      (lambda (m1 m2 args)
        (let loop ([specls1 (%method-specializers m1)]
                   [specls2 (%method-specializers m2)]
                   [args    args])
          (cond [(and (null? specls1) (null? specls2))
                 (if (eq? (%method-qualifier m1) (%method-qualifier m2))
                   (error 'generic
                          "two methods are equally specific in ~e" generic)
                   #f)]
                ;; some methods in this file have less specializers than
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
  (make-method (list <generic>)
    (lambda (call-next-method generic methods)
      (let ([primaries '()] [arounds '()] [befores '()] [afters '()]
            [combination (%generic-combination generic)])
        ;; *** Trick: this (and in <method> above) is the only code that is
        ;; supposed to ever apply a method procedure.  So, the closure that
        ;; will invoke `no-next-method' is named `*no-next-method*' so it is
        ;; identifiable.  The only way to break this would be to call the
        ;; method-procedure directly on an object with such a name.
        (define one-step
          (if combination
            (combination generic)
            (lambda (tail args)
              (lambda newargs
                ;; tail is never null: (null? (cdr tail)) below, and the fact
                ;; that this function is applied on the primaries which are
                ;; never null
                (let ([args (if (null? newargs) args newargs)])
                  (apply (cdar tail)
			 (if (null? (cdr tail))
			     (lambda args
			       (apply no-next-method generic (caar tail) args))
			     (one-step (cdr tail) args))
			 args))))))
        (define ((apply-before/after-method args) method)
          (apply (cdr method)
		 (lambda args
		   (apply no-next-method generic (car method) args))
		 args))
        (define ((call-before-primary-after args) . newargs)
          ;; could supply newargs below, but change before calling befores
          (let ([args (if (null? newargs) args newargs)])
            (for-each (apply-before/after-method args) befores)
            (begin0 ((one-step primaries args))
              (for-each (apply-before/after-method args) afters))))
        (define (one-around-step tail args)
          (if (null? tail)
            (call-before-primary-after args)
            (lambda newargs
              (let ([args (if (null? newargs) args newargs)])
                (apply (cdar tail) (one-around-step (cdr tail) args) args)))))
        ;; first sort by qualifier and pull out method-procedures
        (let loop ([ms methods])
          (unless (null? ms)
            (letsubst ([(push! p)
                        (set! p (cons (cons (car ms)
                                            (%method-procedure (car ms)))
                                      p))])
              (case (%method-qualifier (car ms))
                [(#:primary) (push! primaries)]
                [(#:around)  (push! arounds)]
                [(#:before)  (push! befores)]
                [(#:after)   (push! afters)]
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
               (one-step primaries '())]
              [else (one-around-step arounds '())])))))

(define (make-generic-combination
          #:init [init '()] #:combine [combine cons]
	  #:process-methods [process-methods #f] 
	  #:process-result [process-result #f]
	  #:control [control #f])
  (lambda (generic)
    (lambda (tail dummy-args)
      (let ([tail (if process-methods (process-methods tail) tail)])
        (lambda args
          (let loop ([res init] [tail tail])
            ;; see *no-next-method* trick above
            (let ([*no-next-method*
                   (lambda args (apply no-next-method generic (caar tail) args))])
              (if (null? tail)
                (if process-result (process-result res) res)
                (if control
                  (control loop res
                           (lambda () (apply (cdar tail) *no-next-method* args))
                           (cdr tail))
                  (loop (combine (apply (cdar tail) *no-next-method* args) res)
                        (cdr tail)))))))))))

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
(defsubst (%struct->class c)
  (if (struct-type? c) (struct-type->class c) c))

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
        (memq (%struct->class c) (%class-cpl (%struct->class (class-of x)))))))

(define (class? x) (instance-of? x <class>))
(defsubst (%class? x) (instance-of? x <class>))

(define (specializer? x) (or (class? x) (%singleton? x) (struct-type? x)))

(define (more-specific? c1 c2 arg)
  (if (%singleton? c1)
    (and (eq? (singleton-value c1) arg)
         (not (and (%singleton? c2) (eq? (singleton-value c1) arg))))
    (let ([cc1 (memq (%struct->class c1) (%class-cpl (class-of arg)))])
      (and cc1 (memq (%struct->class c2) (cdr cc1))))))

(add-method initialize
  (make-method (list <top>)
    (lambda (call-next-method object initargs)
      (error 'initialize "can't initialize an instance of ~e"
             (class-of object)))))

(add-method initialize
  (make-method (list <object>)
    (lambda (call-next-method object initargs)
      (let* ([class (class-of object)]
             [field-initializers (%class-field-initializers class)])
        (for-each (lambda (init) (apply init initargs))
                  (%class-initializers class))
        (let loop ([n 0] [inits field-initializers])
          (when (pair? inits)
            (%instance-set! object n (apply (car inits) initargs))
            (loop (+ n 1) (cdr inits))))))))

(add-method initialize
  (make-method (list <class>)
    (lambda (call-next-method class
			      #:name [name '-anonymous-]
			      #:direct-supers [supers '()]
			      #:autoinitargs [autoinitargs #f]
			      #:direct-slots [dslots '()])
      (call-next-method)
      (%set-class-direct-supers!
       class
       (let ([default (*default-object-class*)])
         ;; check valid supers, and always have an object class
         (cond
          [(not default) supers] ; check disabled
          [(or (not supers) (null? supers)) (list default)]
          [(not (list? supers)) (error 'class "bad superclasses: ~e" supers)]
          [else (let ([c (find-if
                          (lambda (c)
                            (not (and (%class? c) (subclass? c default))))
                          supers)])
                  (if c
                    (error 'class "cannot inherit from a ~a, ~e"
                           (if (%class? c) "non-object class" "non-class") c)
                    supers))])))
      (%set-class-direct-slots!
       class
       (map (lambda (s)
	      (if (pair? s)
                  (if (or (not autoinitargs)
			  ;; FIXME
                          #; (getarg (cdr s) #:initarg)
                          (not (symbol? (car s))))
		      s
		      (list* (car s) #:initarg (string->symbol
						(string-append
						 ":" (symbol->string (car s))))
			     (cdr s)))
                  (list s)))
	    dslots))
      (%set-class-cpl!   class (compute-cpl   class))
      (%set-class-slots! class (compute-slots class))
      (%set-class-name!  class name)
      (let* ([nfields 0]
             [field-initializers '()]
             ;; allocator: give me an initializer function, get a slot number
             [allocator (lambda (init)
                          (let ([f nfields])
                            (set! nfields (+ nfields 1))
                            (set! field-initializers
                                  (cons init field-initializers))
                            f))]
             [getters-n-setters (map (lambda (slot)
                                       (cons (car slot)
                                             (compute-getter-and-setter
                                              class slot allocator)))
                                     (%class-slots class))])
        (%set-class-nfields! class nfields)
        (%set-class-field-initializers! class (reverse field-initializers))
        (%set-class-getters-n-setters! class getters-n-setters))
      (%set-class-initializers!
       class (reverse
              (mappend
               (lambda (c)
                 (if (instance-of? c <class>) (%class-initializers c) '()))
               (cdr (%class-cpl class)))))
      (%set-class-valid-initargs! ; for sanity checks
       class 
       ;;; FIXME
       #f #;
       (getarg initargs #:valid-initargs
	       (thunk (mappend (lambda (slot)
				 (getargs (cdr slot) #:initarg))
			       (%class-slots class))))))))

(add-method initialize
  (make-method (list <generic>)
    (lambda (call-next-method generic initargs)
      (call-next-method)
      (%set-generic-methods! generic '())
      (%set-generic-arity!   generic #f #;(getarg initargs #:arity #f)
			     )
      (%set-generic-name!    generic (or #;(getarg initargs #:name) '-anonymous-
				      ))
      (%set-generic-combination! generic #f #; (getarg initargs :combination)
				 )
      (set-instance-proc!    generic
                             (lambda args
                               (raise* make-exn:fail:contract
                                       "~s: no methods added yet"
                                       (%generic-name generic)))))))

(add-method initialize
  (make-method (list <method>)
    (lambda (call-next-method method initargs)
      (call-next-method)
      (%set-method-specializers! method
                                 (map (lambda (c) (%struct->class c))
                                      '() #; (getarg initargs #:specializers)
				      ))
      (%set-method-procedure!    method #f #;(getarg initargs #:procedure)
				 )
      (%set-method-qualifier!    method (or #;(getarg initargs #:qualifier)
                                            ':primary))
      (%set-method-name!         method (or #;(getarg initargs #:name)
                                            '-anonymous-))
      (set-instance-proc!        method (compute-apply-method method)))))

(add-method allocate-instance
  (make-method (list <class>)
    (lambda (call-next-method class initargs)
      (%allocate-instance class (length (%class-field-initializers class))))))

(add-method allocate-instance
  (make-method (list <entity-class>)
    (lambda (call-next-method class initargs)
      (%allocate-entity class (length (%class-field-initializers class))))))

(add-method compute-cpl
  (make-method (list <class>)
    (lambda (call-next-method class)
      (compute-std-cpl class %class-direct-supers))))

(add-method compute-slots
  (make-method (list <class>)
    (lambda (call-next-method class)
      (let ([all-slots   (map %class-direct-slots (%class-cpl class))]
            [final-slots #f])
        (let collect ([to-process (apply append all-slots)]
                      [result '()])
          (if (null? to-process)
            (set! final-slots result)
            (let* ([name   (caar to-process)]
                   [others '()]
                   [remaining-to-process
                    (filter (lambda (o)
                              (if (eq? (car o) name)
                                (begin (set! others (cons (cdr o) others)) #f)
                                #t))
                            to-process)])
              (collect remaining-to-process
                       (cons (cons name (apply append (reverse others)))
                             result)))))
        ;; Sort the slots by order of appearance in cpl, makes them stay in the
        ;; same index, allowing optimizations for single-inheritance
        (let collect ([to-process (apply append (reverse all-slots))]
                      [result '()])
          (cond [(null? to-process) (reverse result)]
                [(assq (caar to-process) result)
                 (collect (cdr to-process) result)]
                [else (collect (cdr to-process)
                               (cons (assq (caar to-process) final-slots)
                                     result))]))))))

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
                 (make-setter-locked! g+s lock
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
                   (make-setter-locked! (car slot) g+s lock
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
    (lambda (call-next-method generic method . args)
      (raise* make-exn:fail:contract
              (concat "~s: no applicable next method to call"
                      (case (%method-qualifier method)
                        [(#:before) " in a `before' method"]
                        [(#:after)  " in an `after' method"]
                        [else ""])
                      " with arguments: ~e")
              (%generic-name generic) args))))
(add-method no-next-method
  (make-method (list (singleton #f) <method>)
    (lambda (call-next-method generic method . args)
      (raise* make-exn:fail:contract
              (concat "~s: no applicable next method in a direct method call"
                      " with arguments: ~e")
              (%method-name method) args))))

(add-method no-applicable-method
  (make-method (list <generic>)
    (lambda (call-next-method generic . args)
      (raise* make-exn:fail:contract
              "~s: no applicable primary methods for arguments ~e, of types ~e"
              (%generic-name generic) args (map class-of args)))))

;;; ---------------------------------------------------------------------------
;;; Customization variables

(define *default-method-class*      (make-parameter <method>))
(define *default-generic-class*     (make-parameter <generic>))
(define *default-class-class*       (make-parameter <class>))
(define *default-entityclass-class* (make-parameter <entity-class>))

(define *default-object-class* (make-parameter #f))

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
           (make-keyword-procedure
	    (lambda (call-next-method class . initargs)
	      (let ([instance (allocate-instance class initargs)])
		(when (*make-safely*) (check-initargs class initargs))
		(initialize instance initargs)
		instance))))]
      [g (make-generic-function 'make)])
  (add-method g m)
  (set! make g))

;; The clean concept behind this is due to Joe Marshall.

(defsubst* (rec-make (name class arg ...) ...)
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
(defsubst (defprimclass primclass) (defprimclass primclass <builtin>)
          (_ primclass supers ...) (define primclass
                                     (make <primitive-class>
                                           #:name          'primclass
                                           #:direct-supers (list supers ...)
                                           #:direct-slots  '())))
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

;;; ---------------------------------------------------------------------------
;;; Some useful predicates.

(define (builtin?  x) (instance-of? x <builtin>))
(define (function? x) (instance-of? x <function>))
(define (generic?  x) (instance-of? x <generic>))
(define (method?   x) (instance-of? x <method>))

;;; ---------------------------------------------------------------------------
||#

