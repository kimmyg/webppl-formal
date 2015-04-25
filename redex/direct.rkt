#lang racket/base
(require redex/reduction-semantics
         "util.rkt")

(define-language L
  [e x n b prim rand
     (λ (x ...) e) 
     (fix x (λ (x ...) e))
     (e e ... ℓ)
     (if e e e)
     (let ([x e]) e)]
  [x variable-not-otherwise-mentioned]
  [n number]
  [b #t #f]
  [prim + - * / = < <= > >=]
  [rand flip beta gaussian]
  [ℓ (variable-prefix ℓ)])

(define-extended-language LM L
  [ς (ev e ρ ι κ)
     (ap κ V)]
  [v n b prim rand
     (clos (λ (x ...) e) ρ)
     (clos (fix x (λ (x ...) e)) ρ)]
  [ω (degenerate v)
     (deterministic prim ω ω)
     (random rand (ω ...))
     (true ω ω)
     (fals ω ω)]
  [V (v ω)]
  [ρ ((x V) ...)]
  [ι (ℓ ...)]
  [κ halt-κ
     (if-κ ρ e e ι κ)
     (ifω-κ V κ)
     (fω-κ ω κ)
     (let-κ x ρ e ι κ)
     (rat-κ ρ (e ...) ℓ ι κ)
     (ran-κ V (V ...) ρ (e ...) ℓ ι κ)])

(define-metafunction LM
  inject : e -> ς
  [(inject e) (ev e () () halt-κ)])

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


#;
(define-metafunction LM
  compose : ω ω -> ω
  [(compose indeterminate ω) ω]
  [(compose (true ω_0 ω_1) ω) (true ω_0 (compose ω_1 ω))]
  [(compose (fals ω_0 ω_1) ω) (fals ω_0 (compose ω_1 ω))])

(define-metafunction LM
  lift : ω ω -> ω
  [(lift (degenerate _) ω) ω]
  [(lift (true ω_0 ω_1) ω) (true ω_0 (lift ω_1 ω))]
  [(lift (fals ω_0 ω_1) ω) (fals ω_0 (lift ω_1 ω))])

(define (make-> O)
  (define-metafunction LM
    apply : V (V ...) ι κ -> ς
    [(apply (prim ω_f) ((n_0 ω_0) (n_1 ω_1)) ι κ)
     (ap (fω-κ ω_f κ) (,((->meta (term prim)) (term n_0) (term n_1)) (deterministic prim ω_0 ω_1)))]
    [(apply (flip ω_f) ((v_p ω_p)) ι κ)
     (ap (fω-κ ω_f κ) (,(backflip (O (term ι)) (term v_p)) (random flip (ω_p))))]
    [(apply (beta ω_f) ((v_α ω_α) (v_β ω_β)) ι κ)
     (ap (fω-κ ω_f κ) (,(backbeta (O (term ι)) (term v_α) (term v_β)) (random beta (ω_α ω_β))))]
    [(apply (gaussian ω_f) ((v_μ ω_μ) (v_σ² ω_σ²)) ι κ)
     (ap (fω-κ ω_f κ) (,(backgaussian (O (term ι)) (term v_μ) (term v_σ²)) (random beta (ω_μ ω_σ²))))]
    [(apply ((clos (λ (x ..._0) e) ρ) ω_f) (V ..._0) ι κ)
     (ev e (ρ-extend* ρ (x ...) (V ...)) ι (fω-κ ω_f κ))]
    [(apply ((clos (fix x_f (λ (x ..._0) e)) ρ) ω_f) (V ..._0) ι κ)
     (ev e (ρ-extend* (ρ-extend ρ x_f ((clos (fix x_f (λ (x ...) e)) ρ)
                                       (degenerate (clos (fix x_f (λ (x ...) e)) ρ))))
                      (x ...) (V ...)) ι (fω-κ ω_f κ))])

  (reduction-relation
   LM
   #:domain ς

   [--> (ev x ρ ι κ)
        (ap κ (ρ-lookup ρ x))
        "variable reference"]
   
   [--> (ev n ρ ι κ)
        (ap κ (n (degenerate n)))
        "numeric constant"]

   [--> (ev b ρ ι κ)
        (ap κ (b (degenerate b)))
        "boolean constant"]

   [--> (ev prim ρ ι κ)
        (ap κ (prim (degenerate prim)))
        "deterministic constant"]

   [--> (ev rand ρ ι κ)
        (ap κ (rand (degenerate rand)))
        "stochastic constant"]

   [--> (ev (λ (x ...) e) ρ ι κ)
        (ap κ (v (degenerate v)))
        (where v (clos (λ (x ...) e) ρ))
        "lambda expression"]

   [--> (ev (fix x_f (λ (x ...) e)) ρ ι κ)
        (ap κ (v (degenerate v)))
        (where v (clos (fix x_f (λ (x ...) e)) ρ))
        "fix expression"]

   [--> (ev (e_f e ... ℓ) ρ ι κ)
        (ev e_f ρ ι (rat-κ ρ (e ...) ℓ ι κ))
        "application expression"]

   [--> (ev (let ([x e_0]) e_1) ρ ι κ)
        (ev e_0 ρ ι (let-κ x ρ e_1 ι κ))
        "let expression"]

   [--> (ev (if e_t e_c e_a) ρ ι κ)
        (ev e_t ρ ι (if-κ ρ e_c e_a ι κ))
        "if expression"]

   [--> (ap (rat-κ ρ_1 () ℓ ι κ) V_f)
        (apply V_f () (ℓ . ι) κ)
        "function without arguments"]
   
   [--> (ap (rat-κ ρ_1 (e_1 e ...) ℓ ι κ) V_f)
        (ev e_1 ρ_1 ι (ran-κ V_f () ρ_1 (e ...) ℓ ι κ))
        "function with argument(s)"]

   [--> (ap (ran-κ V_f (V ...) ρ_1 () ℓ ι κ) V_n)
        (apply V_f (V ... V_n) (ℓ . ι) κ)
        "last argument"]
   
   [--> (ap (ran-κ V_f (V ...) ρ_1 (e_i+1 e ...) ℓ ι κ) V_i)
        (ev e_i+1 ρ_1 ι (ran-κ V_f (V ... V_i) ρ_1 (e ...) ℓ ι κ))
        "inner argument"]
   
   [--> (ap (let-κ x ρ_1 e ι κ) V)
        (ev e (ρ-extend ρ_1 x V) ι κ)
        "let bind"]

   [--> (ap (if-κ ρ_1 e_c e_a ι κ) (v ω))
        (ev e_c ρ_1 ι (ifω-κ (v ω) κ))
        "if-true"
        (side-condition (not (equal? (term v) #f)))]
   
   [--> (ap (if-κ ρ_1 e_c e_a ι κ) (#f ω) )
        (ev e_a ρ_1 ι (ifω-κ (#f ω) κ))
        "if-false"]
   
   [--> (ap (ifω-κ (v_0 ω_0) κ) (v ω))
        (ap κ (v (true ω_0 ω)))
        "if-return-true"
        (side-condition (not (equal? (term v_0) #f)))]
   
   [--> (ap (ifω-κ (#f ω_0) κ) (v ω))
        (ap κ (v (fals ω_0 ω)))
        "if-return-false"]

   [--> (ap (fω-κ ω_f κ) (v ω))
        (ap κ (v (lift ω_f ω)))
        "function return"]))

(provide L inject make->)

(module+ main
  (define -> (make-> (λ (ι) 0.5)))
  
  (apply-reduction-relation* -> (term (inject (flip 0.5 ℓ0))))
  (apply-reduction-relation* -> (term (inject (if (flip 0.5 ℓ0) 2 3))))
  (apply-reduction-relation* -> (term (inject (let ([y (λ (x) x)]) 42))))
  (apply-reduction-relation* -> (term (inject (let ([fact (fix fact (λ (n) (if (= n 0 ℓ0) 1 (* n (fact (- n 1 ℓ1) ℓ2) ℓ3))))])
                                                (fact 3 ℓ4))))))


#;
(module+ main
  (require racket/match
           redex)
  (non-terminal-style 'swiss)

  (define rewriter
    (match-lambda
      [(and LW (lw x l ls c cs u? m?))
       (cond
         [(string? x) LW]
         [(symbol? x) LW]
         [(list? x) (lw (rewriter* x) l ls c cs u? m?)]
         [else (error 'rewriter "unhandled type of ~v" x)])]))
  
  (define rewriter*
    (match-lambda
      [(list (lw "(" l0 ls0 c0 cs0 u?0 m?0) (lw ")" l1 ls1 c1 cs1 u?1 m?1))
       "HA"]
      [(list (lw "(" l0 ls0 c0 cs0 u?0 m?0) (lw tag l1 ls1 c1 cs1 u?1 m?1) args ... rp)
       (append (list (lw tag l0 ls0 c0 cs1 u?1 m?1) (lw "(" l1 ls1 (+ c0 cs1) cs0 u?0 m?0)) (map rewriter args) (list rp))]))

  
  (define unquote-rewriter
    (match-lambda
      [a a]))

  (render-language L "language.ps")
  
  (render-reduction-relation -> "direct-concrete.ps")
  
  #;                                    ;
  (with-compound-rewriters (['ev rewriter*]
  ['ap rewriter*])
  (with-unquote-rewriter unquote-rewriter
  (render-reduction-relation -> "direct-concrete.ps"))))

