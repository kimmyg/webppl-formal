#lang racket
(require "parse.rkt")

(define (flip p) (if (< (random) p) 0 1))
(define (beta) (random))

(struct clos (λ ρ Ω) #:prefab)

(define (update x v ρ)
  (hash-set ρ (var-x x) v))

(define (update* xs vs ρ)
  (foldl update ρ xs vs))

(define (A e ρ)
  (if (ulam? e)
    (clos e ρ)
    (match e

      [(num n)
       n]
      [(href x)
       (case x
         [(*) *]
         [(sub1) sub1]
         [else (error 'A "not for ~a" x)])]
      [(sref x)
       (hash-ref ρ x)])))

(struct branch (v ωv ω) #:transparent)
(struct constant () #:transparent)
(struct deterministic (f ωs) #:transparent)

(define (eval* es ρ Ω)
  (match es
    [(list) (values (list) (list))]
    [(cons e es)
     (let-values ([(v ω) (eval e ρ Ω)]
                  [(vs ωs) (eval* es ρ Ω)])
       (values (cons v vs) (cons ω ωs)))]))

(define (subst ω0 ω1)
  (match ω0
    [(constant) ω1]))

(define (eval e ρ Ω)
  (cond
    [(lam? e)
     (values (clos e ρ Ω) (constant))]
    [else
     (match e
       [(app f es ℓ)
        (let-values ([(vf ωf) (eval f ρ Ω)]
                     [(vs ωs) (eval* es ρ Ω)])
          (if (procedure? vf)
            (values (apply vf vs) (subst ωf (deterministic vf ωs)))
            (match-let ([(clos (lam xs e) ρ Ω) vf])
              (eval e (update* xs vs ρ) (update* xs ωs Ω)))))]
       [(fix f λ)
        (let* ([ph (make-placeholder #f)]
               [g (clos λ (update f ph ρ) (update f (constant) Ω))])
         (placeholder-set! ph g)
         (values (make-reader-graph g) (constant)))]
       [(href x)
        (values (case x
                  [(*) *]
                  [(sub1) sub1]
                  [else (error 'eval "no primitive found: ~a" x)])
                (constant))]
       [(if0 et ec ea)
        (let*-values ([(v0 ω0) (eval et ρ Ω)]
                      [(v1 ω1) (eval (if (zero? v0) ec ea) ρ Ω)])
          (values v1 (branch (zero? v0) ω0 ω1)))]
       [(num n)
        (values n (constant))]
       [(sref x)
        (values (hash-ref ρ x) (hash-ref Ω x))])]))

(define (inject p)
  (eval p (hasheq) (hasheq)))

(inject (P ((λ (fact) (fact 5)) (fix fact (λ (n) (if0 n 1 (* n (fact (sub1 n)))))))))
