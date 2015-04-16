#lang racket
(require redex)

(define-language L
  [e x
     n
     prim
     rand
     (λ (x ...) e)
     (e e ...)
     (let ([x e]) e)
     (if0 e e e)
     (fix e)]
  [n number]
  [prim + - * /]
  [rand flip beta gaussian]
  [x variable-not-otherwise-mentioned])

(define-extended-language LM L
  [ς (ev e ρ κ)
     (ap v ρ κ)]
  [v n prim rand (clos (λ (x ...) e) ρ)]
  [ρ ((x v) ...)]
  [κ halt-κ
     (let-κ x ρ e κ)
     (rat-κ ρ (e ...) κ)
     (ran-κ v (v ...) ρ (e ...) κ)])

(define ->
  (reduction-relation
   LM
   #:domain ς

   [--> (ev x ρ κ)
        (ap (lookup ρ x) ρ κ)]
   
   [--> (ev n ρ κ)
        (ap n ρ κ)]

   [--> (ev prim ρ κ)
        (ap prim ρ κ)]

   [--> (ev rand ρ κ)
        (ap rand ρ κ)]

   [--> (ev (λ (x ...) e) ρ κ)
        (ap (clos (λ (x ...) e) ρ) ρ κ)]

   [--> (ev (e_f e ...) ρ κ)
        (ev e_f ρ (rat-κ ρ (e ...) κ))]

   [--> (ev (let ([x e_0]) e_1) ρ κ)
        (ev e_0 ρ (let-κ x ρ e_1 κ))]

   [--> (ap v ρ_0 (rat-κ ρ_1 () κ))
        (apply v () κ)]
   
   [--> (ap v_f ρ_0 (rat-κ ρ_1 (e_1 e ...) κ))
        (ev e_1 ρ_1 (ran-κ v_f () ρ_1 (e ...) κ))]

   [--> (ap v_n ρ_0 (ran-κ v_f (v ...) ρ_1 () κ))
        (apply v_f (v ... v_n) κ)]
   
   [--> (ap v_i ρ_0 (ran-κ v_f (v ...) ρ_1 (e_i+1 e ...) κ))
        (ev e_i+1 ρ_1 (ran-κ v_f (v ... v_i) ρ_1 (e ...) κ))]
   
   [--> (ap v ρ_0 (let-κ x ρ_1 e κ))
        (ev e (extend ρ_1 x v) κ)]))

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

(define-metafunction LM
  apply : v (v ...) κ -> ς
  [(apply prim (n ...) κ)
   (ap 42 () κ)]
  [(apply (clos (λ (x ..._0) e) ρ) (v ..._0) κ)
   (ev e (extend* ρ (x ...) (v ...)) κ)])

#;(traces -> (term (ev (let ([x 5]) x) () halt-κ)))
#;(apply-reduction-relation* -> (term (ev (+ 2 2) () halt-κ)))
(traces -> (term (ev ((λ (x) (x x)) (λ (y) (y y))) () halt-κ)))

#;(render-reduction-relation -> "direct-concrete.ps")

