#lang racket/base

(define (label p)
  (define (inner e labels)
    (match e
      [(ulam x k e′)
       (let ([labels (hash-set labels e (hash-count labels))])
	 (inner e′ labels))]
      [(klam x e′)
       (let ([labels (hash-set labels e (hash-count labels))])
	 (inner e′ labels))]
      [(uapp f e′ k)
       (let ([labels (hash-set labels e (hash-count labels))])
	 (inner k (inner e′ (inner f labels))))]
      [(kapp k e′)
       (let ([labels (hash-set labels e (hash-count labels))])
	 (inner e′ (inner k labels)))]
      [(uref x)
       (hash-set labels e (hash-count labels))]
      [(num n)
       (hash-set labels e (hash-count labels))])
    (inner p (hasheq))


    (for/hasheq ([(e ℓ) (in-hash (label p0))])
      (values (pp e) ℓ))))
