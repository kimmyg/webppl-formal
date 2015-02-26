#lang racket/base

;; the syntactic discipline (type system)
;; calls take on the type of their body, even though they never "return"
;; continuations have the type A -> R
;; the halt continuation has type R -> R and is in the initial environment

;; we want to restrict continuations from appearing anywhere
;; other than the operator of a continuation call or the
;; continuation of a user call. we may be able to do this simply
;; by restricting the value types.

;; T := Tv | Tk
;; Tv := Nat | Tv Tk -> Tv
;; Tk := Tv -> Tv

;; informal justification that this prevents continuations from
;; being used in a first class way: only types from Tv appear
;; on the right hand side of an arrow.

;; a user call (f e k) has type R if
;; - f has type (A × (B -> R)) -> R
;; - e has type A
;; - k has type B -> R

;; a continuation call (k e) has type R if
;; - k has type A -> R
;; - e has type A

;; a user lambda (λ (x k) e) has type (A × (B -> R)) -> R if
;; assuming that x has type A and k has type B -> R
;; - e has type R

;; a continuation lambda (λ (x) e) has type A -> R if
;; assuming that x has type A
;; - e has type R

;; type inference is different from polymorphism.
;; with type inference, we postulate an unknown
;; type and try to solve for it. we might say
;; that we universally quantify a type variable
;; outside the type system.
;; with polymorphism, a term has a type that
;; is instantiated in a particular context
;; and may be instantiated differently in
;; different contexts in a well-typed way.
;; we might say we universally quantify
;; a type variable inside of the type
;; system.

;; to see the difference, consider typing
;; ((λ (f) ((f (λ (y) y)) (f 1))) (λ (x) x))
;; which has no type in a monomorphic type 
;; system.


(define (>>= v f) (and v (f v)))

(struct T ())

(struct Tv T ())
(struct Nat Tv ())
(struct => Tv (a k r))

(struct Tk T ())
(struct -> Tk (a r))

;; prove that the only continuation variable referenced
;; is the current continuation.
;; this can be done by having two type environments: a
;; standard one for user variables and a singleton one
;; for the continuation variable.
;; shadowing needs to be coordinated: a continuation
;; lambda introduces a data variable (in CPS with no
;; first-class use of continuation, the continuation is
;; not data.) that could shadow the continuation in
;; scope. this leaves no way to return in the evaluation
;; of this code. this is a type error. if the continuation
;; variable shadows a user variable, we simply remove the
;; user variable from the type environment. this can be
;; done unilaterally when introducing a new continuation
;; variable.

(define (typecheck e)
  (define (inner e Γ Γk Tk)
    (match e
      [(ulam x k e)
       (>>= (inner e (hash-set (hash-remove Γ k) x (raise 1)) k )
	    (λ (te) (=> (raise 4) (raise 5) te)))]
      [(klam x e)
       (>>= (inner e (hash-set Γ x (raise 3)) Γk)
	    (λ (te) (-> (raise 6) te)))]
      [(uapp f e k)
       (>>= (inner f Γ Γk)
	    (match-lambda
	     [(=> fa fk fr)
	      (>>= (inner e Γ Γk)
		   (λ (te)
		     (>>= (inner k Γ Γk)
			  (match-lambda
			   [(-> ka kr)
			    (raise 42)]
			   [_ #f]))))]
	     [_ #f]))]
      [(kapp k e)
       (>>= (inner k Γ Γk)
	    (match-lambda
	     [(-> ka kr)
	      (>>= (inner e Γ Γk)
		   (λ (te)
		     (raise 10)))]
	     [_ #f]))]
      [(uref x)
       (if (eq? x Γk) Tk (hash-ref Γ x #f))]))
  (inner e (hasheq) 'halt (fresh T (-> T T))))

(define-syntax-rule (fresh T e)
  (let ([T (gensym 'T)]) e))

(typecheck (P (halt 1)))

