#lang racket/base
(require redex/reduction-semantics)

(define-language L
  [e x
     n
     b
     prim
     rand
     (λ (x ...) e)
     (e e ... ℓ)
     (let ([x e]) e)
     (if e e e)
     (fix x (λ (x ...) e))]
  [n number]
  [b #t #f]
  [ℓ (variable-prefix ℓ)]
  [prim + - * / = < <= > >=]
  [rand flip beta gaussian]
  [x variable-not-otherwise-mentioned])

(define-extended-language LM L
  [ς (ev e ρ ω Ω ι κ)
     (ap κ v ω)]
  [v n b prim rand (clos (λ (x ...) e) ρ Ω) (clos (fix x (λ (x ...) e)) ρ Ω)]
  [ρ ((x v) ...)]
  [ω indeterminate
     (degenerate v)
     (true ω ω)
     (fals ω ω)
     (deterministic prim ω ω)
     (random rand (ω ...))]
  [Ω ((x ω) ...)]
  [ι (ℓ ...)]
  [κ halt-κ
     (if-κ ω ρ Ω e e ι κ)
     (let-κ x ρ Ω e ω ι κ)
     (rat-κ ρ Ω (e ...) ℓ ι κ)
     (ran-κ v ω (v ...) ρ (ω ...) Ω (e ...) ℓ ι κ)])

(define (->meta f)
  (case f
    [(+) +] [(-) -] [(*) *] [(/) /]
    [(=) =]
    [else (error '->meta "not defined for ~a" f)]))

(define-metafunction LM
  inject : e -> ς
  [(inject e) (ev e () indeterminate () () halt-κ)])

(define-metafunction LM
  ρ-lookup : ρ x -> v
  [(ρ-lookup ((x_0 v_0) (x v) ...) x_0) v_0]
  [(ρ-lookup ((x_1 v_1) (x v) ...) x_0) (ρ-lookup ((x v) ...) x_0)])

(define-metafunction LM
  ρ-extend : ρ x v -> ρ
  [(ρ-extend ρ x v)
   ((x v) . ρ)])

(define-metafunction LM
  ρ-extend* : ρ (x ...) (v ...) -> ρ
  [(ρ-extend* ρ () ()) ρ]
  [(ρ-extend* ρ (x_0 x ...) (v_0 v ...))
   (ρ-extend* (ρ-extend ρ x_0 v_0) (x ...) (v ...))])

(define-metafunction LM
  Ω-lookup : Ω x -> ω
  [(Ω-lookup ((x_0 ω_0) (x ω) ...) x_0) ω_0]
  [(Ω-lookup ((x_1 ω_1) (x ω) ...) x_0) (Ω-lookup ((x ω) ...) x_0)])

(define-metafunction LM
  Ω-extend : Ω x ω -> Ω
  [(Ω-extend Ω x ω)
   ((x ω) . Ω)])

(define-metafunction LM
  Ω-extend* : Ω (x ...) (ω ...) -> Ω
  [(Ω-extend* Ω () ()) Ω]
  [(Ω-extend* Ω (x_0 x ...) (ω_0 ω ...))
   (Ω-extend* (Ω-extend Ω x_0 ω_0) (x ...) (ω ...))])

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

(require math/distributions)

(define (backflip x p) (not (zero? (inexact->exact (flbernoulli-inv-cdf p x #f #f)))))
(define (backbeta x α β) (flbeta-inv-cdf α β x #f #f))
(define (backgaussian x μ σ²) (flnormal-inv-cdf μ (sqrt σ²) x #f #f))

(define (make-> O)
  (define-metafunction LM
    apply : v ω (v ...) (ω ...) ι κ -> ς
    [(apply prim ω_f (n_0 n_1) (ω_0 ω_1) ι κ)
     (ap κ ,((->meta (term prim)) (term n_0) (term n_1)) (lift ω_f (deterministic prim ω_0 ω_1)))]
    [(apply flip ω_f (v_p) (ω_p) ι κ)
     (ap κ ,(backflip (O (term ι)) (term v_p)) (lift ω_f (random flip (ω_p))))]
    [(apply beta ω_f (v_α v_β) (ω_α ω_β) ι κ)
     (ap κ ,(backbeta (O (term ι)) (term v_α) (term v_β)) (lift ω_f (random beta (ω_α ω_β))))]
    [(apply beta ω_f (v_μ v_σ²) (ω_μ ω_σ²) ι κ)
     (ap κ ,(backgaussian (O (term ι)) (term v_μ) (term v_σ²)) (lift ω_f (random beta (ω_μ ω_σ²))))]
    [(apply (clos (λ (x ..._0) e) ρ Ω) ω_f (v ..._0) (ω ..._0) ι κ)
     (ev e (ρ-extend* ρ (x ...) (v ...)) (lift ω_f indeterminate) (Ω-extend* Ω (x ...) (ω ...)) ι κ)]
    [(apply (clos (fix x_f (λ (x ..._0) e)) ρ Ω) ω_f (v ..._0) (ω ..._0) ι κ)
     (ev e
         (ρ-extend* (ρ-extend ρ x_f (clos (fix x_f (λ (x ...) e)) ρ Ω)) (x ...) (v ...))
         (lift ω_f indeterminate)
         (Ω-extend* (Ω-extend Ω x_f (degenerate (clos (fix x_f (λ (x ...) e)) ρ Ω))) (x ...) (ω ...))
         ι κ)])

  (reduction-relation
   LM
   #:domain ς

   [--> (ev x ρ ω Ω ι κ)
        (ap κ (ρ-lookup ρ x) (compose ω (Ω-lookup Ω x)))
        "variable reference"]
   
   [--> (ev n ρ ω Ω ι κ)
        (ap κ n (compose ω (degenerate n)))
        "numeric constant"]

   [--> (ev prim ρ ω Ω ι κ)
        (ap κ prim (compose ω (degenerate prim)))
        "deterministic constant"]

   [--> (ev rand ρ ω Ω ι κ)
        (ap κ rand (compose ω (degenerate rand)))
        "stochastic constant"]

   [--> (ev (λ (x ...) e) ρ ω Ω ι κ)
        (ap κ (clos (λ (x ...) e) ρ Ω) (compose ω (degenerate (clos (λ (x ...) e) ρ Ω))))
        "lambda expression"]

   [--> (ev (fix x_f (λ (x ...) e)) ρ ω Ω ι κ)
        (ap κ (clos (fix x_f (λ (x ...) e)) ρ Ω) (compose ω (degenerate (clos (fix x_f (λ (x ...) e)) ρ Ω))))
        "fix expression"]

   [--> (ev (e_f e ... ℓ) ρ ω Ω ι κ)
        (ev e_f ρ ω Ω ι (rat-κ ρ Ω (e ...) ℓ ι κ))
        "application expression"]

   [--> (ev (let ([x e_0]) e_1) ρ ω Ω ι κ)
        (ev e_0 ρ indeterminate Ω ι (let-κ x ρ Ω e_1 ω ι κ))
        "let expression"]

   [--> (ev (if e_t e_c e_a) ρ ω Ω ι κ)
        (ev e_t ρ indeterminate Ω ι (if-κ ω ρ Ω e_c e_a ι κ))
        "if expression"]

   [--> (ap (rat-κ ρ_1 Ω_1 () ℓ ι κ) v_f ω_f)
        (apply v_f ω_f () () (ℓ . ι) κ)
        "function without arguments"]
   
   [--> (ap (rat-κ ρ_1 Ω_1 (e_1 e ...) ℓ ι κ) v_f ω_f)
        (ev e_1 ρ_1 indeterminate Ω_1 ι (ran-κ v_f ω_f () ρ_1 () Ω_1 (e ...) ℓ ι κ))
        "function with argument(s)"]

   [--> (ap (ran-κ v_f ω_f (v ...) ρ_1 (ω ...) Ω_1 () ℓ ι κ) v_n ω_n)
        (apply v_f ω_f (v ... v_n) (ω ... ω_n) (ℓ . ι) κ)
        "last argument"]
   
   [--> (ap (ran-κ v_f ω_f (v ...) ρ_1 (ω ...) Ω_1 (e_i+1 e ...) ℓ ι κ) v_i ω_i)
        (ev e_i+1 ρ_1 indeterminate Ω_1 ι (ran-κ v_f ω_f (v ... v_i) ρ_1 (ω ... ω_i) Ω_1 (e ...) ℓ ι κ))
        "inner argument"]
   
   [--> (ap (let-κ x ρ_1 Ω_1 e ω_0 ι κ) v ω)
        (ev e (ρ-extend ρ_1 x v) ω_0 (Ω-extend Ω_1 x ω) ι κ)
        "let bind"]

   [--> (ap (if-κ ω_0 ρ_1 Ω_1 e_c e_a ι κ) v ω)
        (ev e_c ρ_1 (compose ω_0 (true ω indeterminate)) Ω_1 ι κ)
        "if-true"
        (side-condition (not (equal? (term v) #f)))]
   
   [--> (ap (if-κ ω_0 ρ_1 Ω_1 e_c e_a ι κ) #f ω)
        (ev e_a ρ_1 (compose ω_0 (fals ω indeterminate)) Ω_1 ι κ)
        "if-false"]))

(define -> (make-> (λ (ι) 0.5)))




(apply-reduction-relation* -> (term (inject (flip 0.5 ℓ0))))
(apply-reduction-relation* -> (term (inject (if (flip 0.5 ℓ0) 2 3))))
(apply-reduction-relation* -> (term (inject (let ([y (λ (x) x)])
                                              42))))
(apply-reduction-relation* -> (term (inject (let ([fact (fix fact (λ (n) (if (= n 0 ℓ0) 1 (* n (fact (- n 1 ℓ1) ℓ2) ℓ3))))])
                                              (fact 3 ℓ4)))))


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
  
  #;
  (with-compound-rewriters (['ev rewriter*]
  ['ap rewriter*])
  (with-unquote-rewriter unquote-rewriter
    (render-reduction-relation -> "direct-concrete.ps"))))




'(ap (if-κ indeterminate
          ((n 3)
           (fact (clos (fix fact (λ (n)
                                   (if (= n 0 ℓ0)
                                     1
                                     (* n (fact (- n 1 ℓ1) ℓ2) ℓ3))))
                       () ())))
          ((n (degenerate 3))
           (fact (degenerate (clos (fix fact (λ (n)
                                               (if (= n 0 ℓ0)
                                                 1
                                                 (* n (fact (- n 1 ℓ1) ℓ2) ℓ3))))
                                   () ()))))
          1
          (* n (fact (- n 1 ℓ1) ℓ2) ℓ3)
          (ℓ4)
          halt-κ)
    #f
    (deterministic = (degenerate 3) (degenerate 0)))
'(apply = (degenerate =) (3 0) ((degenerate 3) (degenerate 0)) (ℓ0 ℓ4) (if-κ indeterminate ((n 3) (fact (clos (fix fact (λ (n) (if (= n 0 ℓ0) 1 (* n (fact (- n 1 ℓ1) ℓ2) ℓ3)))) () ()))) ((n (degenerate 3)) (fact (degenerate (clos (fix fact (λ (n) (if (= n 0 ℓ0) 1 (* n (fact (- n 1 ℓ1) ℓ2) ℓ3)))) () ())))) 1 (* n (fact (- n 1 ℓ1) ℓ2) ℓ3) (ℓ4) halt-κ))
