#lang racket
(require "parse.rkt")

(define (flip p) (if (< (random) p) 0 1))
(define (beta) (random))

(struct clos (λ ρ) #:prefab)

(struct kont () #:prefab)
(struct halt kont () #:prefab)
(struct fram kont (e ρ κ) #:prefab)

(define (update x v ρ)
  (hash-set ρ (var-x x) v))

(define (A e ρ)
  (if (ulam? e)
    (clos e ρ)
    (match e
      [(fix f λ)
       (let* ([ph (make-placeholder #f)]
              [g (clos λ (update f ph ρ))])
         (placeholder-set! ph g)
         (make-reader-graph g))]
      [(num n)
       n]
      [(href x)
       (case x
         [(*) *]
         [(sub1) sub1]
         [else (error 'A "not for ~a" x)])]
      [(sref x)
       (hash-ref ρ x)])))

(define (D e Ω)
  (match e))

(define (K κ0 ρ κ)
  (cond
    [(kref? κ0) κ]
    [(klam? κ0) (fram κ0 ρ κ)]
    [else
     (error 'K "not for ~a" κ0)]))

(define see
  (match-lambda
    [(halt) null]
    [(fram κ0 ρ κ)
     (cons (unP κ0) (see κ))]))

(define (eval e ρ Ω H κ)
  (displayln (see κ))
  (match e
    [(if0 t c a)
     (let ([v (zero? (A t ρ))]
           [ω (zero* (D t Ω))])
       (if v
         (eval c ρ Ω (cons (branch #t ω)) κ)
         (eval a ρ Ω (cons (branch #f ω)) κ)))]
    [(kapp κ0 e)
     (kappl (K κ0 ρ κ) (A e ρ))]
    [(uapp f es κ0 ℓ)
     (uappl (A f ρ) (map (λ (e) (A e ρ)) es) (K κ0 ρ κ))]))

(define (uappl f vs κ)
  (if (procedure? f)
    (kappl κ (apply f vs))
    (match-let ([(clos (ulam xs k e) ρ) f])
      (eval e (foldl update ρ xs vs) κ))))

(define (kappl κ v)
  (match κ
    [(halt) v]
    [(fram (klam x e) ρ Ω H κ)
     (eval e (update x v ρ) Ω H κ)]))

(define (inject p)
  (uappl (A p (hasheq)) null (halt)))

(inject (CPS (P ((λ (fact) (fact 5)) (fix fact (λ (n) (if0 n 1 (* n (fact (sub1 n))))))))))
