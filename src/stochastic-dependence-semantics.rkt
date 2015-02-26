#lang racket

(struct ref (x))
(struct lam (x e))
(struct app (f e ℓ))
(struct erp ())

(struct clos (λ ρ))

(struct CEKT (e ρ κ ι))

(define fresh-ℓ
  (let ([i 0]) (λ () (begin0 i (set! i (add1 i))))))

(define-syntax P
  (syntax-rules (λ ERP)
    [(_ (λ (x) e)) (lam 'x (P e))]
    [(_ (f e)) (app (P f) (P e) (fresh-ℓ))]
    [(_ ERP) (erp)]
    [(_ x) (ref 'x)]))

(P ((λ (b) (((b (λ (z) ERP)) (λ (z) ERP)) (λ (z) z))) ERP))
