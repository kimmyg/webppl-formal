#lang racket
(require redex)

(define-language L
  [e x
     n
     prim
     rand
     (λ (x ...) e)
     (e e ... ℓ)
     (let ([x e]) e)
     (if0 e e e)
     (fix e)]
  [n number]
  [ℓ (variable-prefix ℓ)]
  [prim + - * /]
  [rand flip beta gaussian]
  [x variable-not-otherwise-mentioned])

(define-extended-language LM L
  [ς (ev e ρ ι κ)
     (ap κ v)]
  [v n prim rand (clos (λ (x ...) e) ρ)]
  [ρ ((x v) ...)]
  [ι (ℓ ...)]
  [κ halt-κ
     (let-κ x ρ e ι κ)
     (rat-κ ρ (e ...) ℓ ι κ)
     (ran-κ v (v ...) ρ (e ...) ℓ ι κ)])

(define (->meta f)
  (case f [(+) +] [(-) -] [(*) *] [(/) /] [else (error '->meta "not defined for ~a" f)]))

(define-metafunction LM
  lookup : ρ x -> v
  [(lookup ((x_0 v_0) (x v) ...) x_0) v_0]
  [(lookup ((x_1 v_1) (x v) ...) x_0) (lookup ((x v) ...) x_0)])

(define-metafunction LM
  extend : ρ x v -> ρ
  [(extend ρ x v)
   ((x v) . ρ)])

(define-metafunction LM
  extend* : ρ (x ...) (v ...) -> ρ
  [(extend* ρ () ()) ρ]
  [(extend* ρ (x_0 x ...) (v_0 v ...))
   (extend* (extend ρ x_0 v_0) (x ...) (v ...))])

(require math/distributions)

(define (backflip x p) (flbernoulli-inv-cdf p x #f #f))
(define (backbeta x α β) (flbeta-inv-cdf α β x #f #f))
(define (backgaussian x μ σ²) (flnormal-inv-cdf μ (sqrt σ²) x #f #f))

(define (make-> O)
  (define-metafunction LM
    apply : v (v ...) ι κ -> ς
    [(apply prim (n_0 n_1) ι κ)
     (ap κ ,((->meta (term prim)) (term n_0) (term n_1)))]
    [(apply flip (v_p) ι κ)
     (ap κ ,(backflip (O (term ι)) (term v_p)))]
    [(apply beta (v_α v_β) ι κ)
     (ap κ ,(backbeta (O (term ι)) (term v_α) (term v_β)))]
    [(apply beta (v_μ v_σ²) ι κ)
     (ap κ ,(backgaussian (O (term ι)) (term v_μ) (term v_σ²)))]
    [(apply (clos (λ (x ..._0) e) ρ) (v ..._0) ι κ)
     (ev e (extend* ρ (x ...) (v ...)) ι κ)])

  (reduction-relation
   LM
   #:domain ς

   [--> (ev x ρ ι κ)
        (ap κ (lookup ρ x))]
   
   [--> (ev n ρ ι κ)
        (ap κ n)]

   [--> (ev prim ρ ι κ)
        (ap κ prim)]

   [--> (ev rand ρ ι κ)
        (ap κ rand)]

   [--> (ev (λ (x ...) e) ρ ι κ)
        (ap κ (clos (λ (x ...) e) ρ))]

   [--> (ev (e_f e ... ℓ) ρ ι κ)
        (ev e_f ρ ι (rat-κ ρ (e ...) ℓ ι κ))]

   [--> (ev (let ([x e_0]) e_1) ρ ι κ)
        (ev e_0 ρ ι (let-κ x ρ e_1 ι κ))]

   [--> (ap (rat-κ ρ_1 () ℓ ι κ) v_f)
        (apply v_f (ℓ . ι) κ)]
   
   [--> (ap (rat-κ ρ_1 (e_1 e ...) ℓ ι κ) v_f)
        (ev e_1 ρ_1 ι (ran-κ v_f () ρ_1 (e ...) ℓ ι κ))]

   [--> (ap (ran-κ v_f (v ...) ρ_1 () ℓ ι κ) v_n)
        (apply v_f (v ... v_n) (ℓ . ι) κ)]
   
   [--> (ap (ran-κ v_f (v ...) ρ_1 (e_i+1 e ...) ℓ ι κ) v_i)
        (ev e_i+1 ρ_1 ι (ran-κ v_f (v ... v_i) ρ_1 (e ...) ℓ ι κ))]
   
   [--> (ap (let-κ x ρ_1 e ι κ) v)
        (ev e (extend ρ_1 x v) ι κ)]))

(define -> (make-> (λ (ι) 0.5)))




#;(traces -> (term (ev (let ([x 5]) x) () halt-κ)))
(apply-reduction-relation* -> (term (ev (flip 0.5 ℓ0) () () halt-κ)))
#;(traces -> (term (ev ((λ (x) (x x ℓ1)) (λ (y) (y y ℓ2)) ℓ0) () () halt-κ)))



#;(render-reduction-relation -> "direct-concrete.ps")

