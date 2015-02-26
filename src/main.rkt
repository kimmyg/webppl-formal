#lang racket
(require "parse.rkt")

(define (Ah e f h)
  (if (or (ulam? e)
	  (klam? e))
    (seteq e)
    (match e
      [(href x)
       (hash-ref h x)]
      [(sref x)
       (seteq (hash-ref f x))])))

(define p0 (P (λ (x k1) (k1 (λ (y k2) (x y (λ (u) (x u k2))))))))


(unP p0)
#;(eval p0 1)
#;(eval (P (λ (x k) (k x))) 42)
#;(eval (P (λ (f k) (f 25 k))) (cons (P (λ (x k) (k x))) (hasheq)))

#;(sref? (uapp-f (ulam-e (kapp-e (ulam-e p0)))))
#;(sref? (uapp-e (ulam-e (kapp-e (ulam-e p0)))))
