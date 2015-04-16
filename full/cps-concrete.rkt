#lang racket
(require "parse.rkt")

(define (bernoulli p) (if (< (random) p) 0 1))
(define (beta) (random))

(struct clos (λ ρ Ω) #:prefab)

(struct Γ ())
(struct halt Γ ())
(struct fram Γ (f ρ ω Ω ι κ))

(define (extend x v ρ)
  (hash-set ρ (var-x x) v))

(define (extend* xs vs ρ)
  (foldl extend ρ xs vs))

(define (A e ρ Ω)
  (if (ulam? e)
    (values (clos e ρ Ω) (constant))
    (match e
      [(fix f λ)
       (let* ([ph (make-placeholder #f)]
              [g (clos λ (extend f ph ρ) (extend f (constant) Ω))])
         (placeholder-set! ph g)
         (values (make-reader-graph g) (constant)))]
      [(num n)
       (values n (constant))]
      [(or (href x) (sref x))
       (if (hash-has-key? ρ x)
         (values (hash-ref ρ x)
                 (hash-ref Ω x))
         (values (case x
                   [(*) *]
                   [(add1) add1]
                   [(sub1) sub1]
                   [(bernoulli) bernoulli]
                   [else (error 'A "no href for ~a" x)])
                 (constant)))])))

(define (A* es ρ Ω)
  (match es
    [(list)
     (values (list) (list))]
    [(cons e es)
     (let-values ([(v ω) (A e ρ Ω)]
                  [(vs ωs) (A* es ρ Ω)])
       (values (cons v vs) (cons ω ωs)))]))

(struct hole () #:transparent)
(struct branch (v ω ωv) #:transparent)
(struct constant () #:transparent)
(struct deterministic (f ι ωs) #:transparent)
(struct stochastic (D ι ωs) #:transparent)

(define reroot
  (match-lambda
    [(constant)
     (hole)]))

(define (compose ω0 ω1)
  (match ω0
    [(or (constant)
         (hole))
     ω1]
    [(branch v ω ω0)
     (branch v ω (compose ω0 ω1))]))

(define (Aκ κ0 ρ ω Ω ι κ)
  (if (kref? κ0)
    (values κ ω)
    (values (fram κ0 ρ ω Ω ι κ) (hole))))

(define (eval e ρ ω Ω ι κ)
  (match e
    [(if0 et ec ea)
     (let-values ([(v ωv) (A et ρ Ω)])
       (eval (if (zero? v) ec ea) ρ (compose ω (branch (zero? v) ωv (hole))) Ω ι κ))]
    [(kapp κ0 e)
     (let-values ([(κ ω) (Aκ κ0 ρ ω Ω ι κ)])
       (let-values ([(v ωv) (A e ρ Ω)])
         (kappl κ v (compose ω ωv))))]
    [(uapp f es κ0 ℓ)
     (let-values ([(κ ω) (Aκ κ0 ρ ω Ω ι κ)])
       (let-values ([(f ωf) (A f ρ Ω)]
                  [(vs ωs) (A* es ρ Ω)])
         (uappl f vs ωs (compose ω (reroot ωf)) (cons ℓ ι) κ)))]
    [(usam D θs κ0 ℓ)
     (let-values ([(κ ω) (Aκ κ0 ρ ω Ω ι κ)])
       (let-values ([(D ωD) (A D ρ Ω)]
                    [(θs ωs) (A* θs ρ Ω)])
         (kappl κ (apply D θs) (compose ω (compose (reroot ωD) (stochastic D (cons ℓ ι) ωs))))))]))

(define (uappl f vs ωs ω ι κ)
  (match f
    [(? procedure?)
     (kappl κ (apply f vs) (compose ω (deterministic f ι ωs)))]
    [(clos (ulam xs k e) ρ Ω)
     (let ([ρ (extend* xs vs ρ)]
           [Ω (extend* xs ωs Ω)])
       (eval e ρ ω Ω ι κ))]))

(define (kappl κ v ωv)
  (match κ
    [(fram (klam x e) ρ ω Ω ι κ)
     (let ([ρ (extend x v ρ)]
           [Ω (extend x ωv Ω)])
       (eval e ρ ω Ω ι κ))]
    [(halt)
     (values v ωv)]))

(define (inject p)
  (let-values ([(f ωf) (A p (hasheq) (hasheq))])
    (uappl f null null (hole) null (halt))))

(define p0
  (P ((λ (fact) (fact 5)) (fix fact (λ (n) (if0 n 1 (* n (fact (sub1 n)))))))))

(define p1
  (P (if0 (sample bernoulli 1/2) ((λ (x) 42) (sample bernoulli 1/3)) 35)))

(define p2
  (P ((λ (f) ((λ (g) ((λ (x) 42) (if0 (sample bernoulli 1/2) (f) (g))))
              (λ () (sample bernoulli 1/3))))
      (λ () (sample bernoulli 1/5)))))

(define p3
  (P ((λ (geom) (geom 1/3))
      (fix geom (λ (p) (if0 (sample bernoulli p) 0 (add1 (geom p))))))))

(define p4
  (P (if0 (sample bernoulli 1/2) ((λ (x) 42) (if0 (sample bernoulli 1/3) 12 13)) 35)))

(define (run p)
  (let ([cpsp (CPS p)])
    (displayln (unP p))
    (displayln (unP cpsp))
    (inject cpsp)))

(run p4)


