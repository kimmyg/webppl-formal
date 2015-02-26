#lang racket/base
(require racket/match
	 "parse.rkt")

(provide (all-defined-out))

(define (stxfold h u stx)
  (match stx
    [(num n) (h stx u)]
    [(ulam x k e) (stxfold h (h stx u) e)]
    [(uapp f e k)
     (stxfold h (stxfold h (stxfold h (h stx u) f) e) k)]
    [(klam x e) (stxfold h (h stx u) e)]
    [(kapp k e) (stxfold h (stxfold h (h stx u) e) k)]
    [(href x) (h stx u)]
    [(sref k) (h stx u)]))

(define (make-ℓ p)
  (let ([ℓs (stxfold (λ (e ℓs) (hash-set ℓs e (hash-count ℓs)))
		     (hasheq)
		     p)])
    (λ (e) (hash-ref ℓs e #f))))
