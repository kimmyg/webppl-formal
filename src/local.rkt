#lang racket/base
(require racket/match
	 racket/set
	 "parse.rkt")

(struct UApplyEntry (proc d σ))	; about to enter function body
(struct CApplyInner/Return (proc d ρ σ))

(struct CEvalInner (k e ρ σ)) ; CEval with continuation operator a lambda
(struct CEvalExit (e ρ σ)) ; CEval with continuation operator a variable

(struct UEvalCall (f e k ρ σ)) ; UEval with continuation argument a lambda
(struct UEvalExit (f e ρ σ)) ; UEval with continuation argument a variable

(struct clos (λ ρ))

(define (I p d)
  (UApplyEntry (clos p (hasheq)) d empty-σ))

(define empty-ρ (hasheq))
(define empty-σ (hasheq))

(define (ρ-join ρ x d)
  (hash-update ρ x (λ (d0) (set-union d0 d)) (set)))
(define (σ-join σ x d)
  (hash-update σ x (λ (d0) (set-union d0 d)) (set)))

(define ρ-ref hash-ref)
(define σ-ref hash-ref)

(define (Au e ρ σ)
  (if (ulam? e)
    (set e)
    (match e
      [(href x)
       (σ-ref σ x)]
      [(sref x)
       (ρ-ref ρ x)])))

(define (make- c ρ σ)
  (match-let ([(kapp k e) c])
    (if (kref? k)
      (CEvalExit e ρ σ)
      (CEvalInner k e ρ σ))))

(define =>
  (match-lambda
   [(UEvalCall f e k ρ σ)
    (let ([d (Au e ρ σ)])
      (for/list ([f (in-set (Au f ρ σ))])
	(UApplyEntry (clos f (hasheq)) d σ)))]
   [(UApplyEntry (clos (ulam x k e) ρ) d σ)
    (list (match x
	    [(svar x)
	     (make- e (ρ-join ρ x d) σ)]
	    [(hvar x)
	     (make- e ρ (σ-join σ x d))]))]
   [(CEvalInner k e ρ σ)
    (CApplyInner/Return k (Au e ρ σ) ρ σ)]
   [(CEvalExit e ρ σ)
    (list)]
   [(CApplyInner/Return (klam (kvar x) e) d ρ σ)
    (make- e (ρ-join ρ x d) σ)]))

(define seen (set))
(define work (set))

(apply append (map => (=> (I (P (λ (x k) (k x))) (set 42)))))
