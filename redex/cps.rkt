#lang racket/base
(require redex/reduction-semantics
         "util.rkt")

(define-language L
  [ae x n b prim rand
      (λ (x ... k) e)
      (fix x (λ (x ... k) e))]
  [e (ae ae ... K ℓ)
     (if ae e e)
     (K ae)]
  [x variable-not-otherwise-mentioned]
  [n number]
  [b #t #f]
  [prim + - * / = < <= > >=]
  [rand flip beta gaussian]
  [ℓ (variable-prefix ℓ)]
  [k (variable-prefix k)]
  [K k (μ (x) e)])

(define-extended-language LM L
  [ς (ev e ρ ι κ)
     (ap κ (v ω))]
  [v n b prim rand
     (clos (λ (x ... k) e) ρ)
     (clos (fix x (λ (x ... k) e)) ρ)]
  [ω (degenerate v)
     (deterministic prim ω ω)
     (random rand (ω ...))
     (true ω ω)
     (fals ω ω)]
  [V (v ω)]
  [ρ ((x V) ...)]
  [ι (ℓ ...)]
  [κ halt-κ
     (fram-κ (μ (x) e) ρ ι κ)
     (ifω-κ V κ)
     (fω-κ ω κ)])

(define-metafunction LM
  inject : (λ (k) e) -> ς
  [(inject (λ (k) e)) (ev e () () halt-κ)])

(define-metafunction LM
  ρ-lookup : ρ x -> V
  [(ρ-lookup ((x_0 V_0) (x V) ...) x_0) V_0]
  [(ρ-lookup ((x_1 V_1) (x V) ...) x_0) (ρ-lookup ((x V) ...) x_0)])

(define-metafunction LM
  ρ-extend : ρ x V -> ρ
  [(ρ-extend ρ x V)
   ((x V) . ρ)])

(define-metafunction LM
  ρ-extend* : ρ (x ...) (V ...) -> ρ
  [(ρ-extend* ρ () ()) ρ]
  [(ρ-extend* ρ (x_0 x ...) (V_0 V ...))
   (ρ-extend* (ρ-extend ρ x_0 V_0) (x ...) (V ...))])

(define-metafunction LM
  compose : K ρ ι κ -> κ
  [(compose k ρ ι κ) κ]
  [(compose (μ (x) e) ρ ι κ)
   (fram-κ (μ (x) e) ρ ι κ)])

(define-metafunction LM
  lift : ω ω -> ω
  [(lift (degenerate _) ω) ω]
  [(lift (true ω_0 ω_1) ω) (true ω_0 (lift ω_1 ω))]
  [(lift (fals ω_0 ω_1) ω) (fals ω_0 (lift ω_1 ω))])

(define-metafunction LM
  A : ae ρ -> (v ω)
  [(A x ρ) (ρ-lookup ρ x)]
  [(A n ρ) (n (degenerate n))]
  [(A b ρ) (b (degenerate b))]
  [(A prim ρ) (prim (degenerate prim))]
  [(A rand ρ) (rand (degenerate rand))]
  [(A (λ (x ... k) e) ρ)
   ((clos (λ (x ... k) e) ρ)
    (degenerate (clos (λ (x ... k) e) ρ)))]
  [(A (fix x_f (λ (x ... k) e)) ρ)
   ((clos (fix x_f (λ (x ... k) e)) ρ)
    (degenerate (clos (fix x_f (λ (x ... k) e)) ρ)))])

(define (make-> O)
  (define-metafunction LM
    apply : (v ω) ((v ω) ...) ι κ -> ς
    [(apply (prim ω_f) ((n_0 ω_0)(n_1 ω_1)) ι κ)
     (ap (fω-κ ω_f κ) (,((->meta (term prim)) (term n_0) (term n_1)) (deterministic prim ω_0 ω_1)))]
    [(apply (flip ω_f) ((v_p ω_p)) ι κ)
     (ap (fω-κ ω_f κ) (,(backflip (O (term ι)) (term v_p)) (random flip (ω_p))))]
    [(apply (beta ω_f) ((v_α ω_α) (v_β ω_β)) ι κ)
     (ap (fω-κ ω_f κ) (,(backbeta (O (term ι)) (term v_α) (term v_β)) (random beta (ω_α ω_β))))]
    [(apply (beta ω_f) ((v_μ ω_μ) (v_σ² ω_σ²)) ι κ)
     (ap (fω-κ ω_f κ) (,(backgaussian (O (term ι)) (term v_μ) (term v_σ²)) (random beta (ω_μ ω_σ²))))]
    [(apply ((clos (λ (x ..._0 k) e) ρ) ω_f) (V ..._0) ι κ)
     (ev e (ρ-extend* ρ (x ...) (V ...)) ι (fω-κ ω_f κ))]
    [(apply ((clos (fix x_f (λ (x ..._0 k) e)) ρ) ω_f) (V ..._0) ι (fω-κ ω_f κ))
     (ev e (ρ-extend* (ρ-extend ρ x_f ((clos (fix x_f (λ (x ...) e)) ρ) ω_f)) (x ...) (V ...)) ι (fω-κ ω_f κ))])

  (reduction-relation
   LM
   #:domain ς

   [--> (ev (ae_f ae ... K ℓ) ρ ι κ)
        (apply (A ae_f ρ) ((A ae ρ) ...) ι (compose K ρ ι κ))
        "function call"]

   [--> (ev (K ae) ρ ι κ)
        (ap (compose K ρ ι κ) (A ae ρ))
        "continuation call"]

   [--> (ev (if ae_t e_c e_a) ρ ι κ)
        (ev e_c ρ ι (ifω-κ (v ω) κ))
        (where (v ω) (A ae_t ρ))
        (side-condition (not (equal? (term v) #f)))
        "if expression (true)"]

   [--> (ev (if ae_t e_c e_a) ρ ι κ)
        (ev e_a ρ ι (ifω-κ (#f ω_v) κ))
        (where (#f ω_v) (A ae_t ρ))
        "if expression (false)"]

   [--> (ap (fω-κ ω_f κ) (v ω))
        (ap κ (v (lift ω_f ω)))
        "function return"]
   
   [--> (ap (fram-κ (μ (x) e) ρ ι κ) V)
        (ev e (ρ-extend ρ x V) ι κ)
        "return"]

   [--> (ap (ifω-κ (v_0 ω_0) κ) (v ω))
        (ap κ (v (true ω_0 ω)))
        (side-condition (not (equal? (term v_0) #f)))
        "if return (true)"]

   [--> (ap (ifω-κ (#f ω_0) κ) (v ω))
        (ap κ (v (fals ω_0 ω)))
        "if return (false)"]))

(provide L make-> inject)
