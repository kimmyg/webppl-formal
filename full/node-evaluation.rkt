#lang racket
(require "parse.rkt")

(struct node () #:transparent)
(struct rand node (deps) #:transparent)
(struct true node (sel) #:transparent)
(struct fals node (sel) #:transparent)
(struct dete node (f dis) #:transparent)

(struct sour () #:transparent)
(struct parameter sour (n) #:transparent)
(struct result sour (ℓ) #:transparent)
(struct degenerate sour (v) #:transparent)

(define (eval f)
  (define (D e ρ)
    (match e
      [(num n)
       (degenerate n)]
      [(sref x)
       (hash-ref ρ x)]))
  (define (appl κ v ρ H)
    (match κ
      [(kref κ)
       (cons v H)]
      [(klam x e)
       (eval e (hash-set ρ (var-x x) v) H)]))
  (define (eval e ρ H)
    (match e
      [(uapp f es κ ℓ)
       (appl κ (result ℓ) ρ H)]
      [(kapp κ e)
       (appl κ (D e ρ) ρ H)]
      [(if0 c t a)
       (let ([v (D c ρ)])
         (list (eval t ρ (cons (true v) H))
               (eval a ρ (cons (fals v) H))))]))
  (match-let ([(ulam '() k0 (kapp k1 (ulam xs k2 e))) f])
    (let ([ρ (for/hasheq ([x (in-list xs)]
                          [i (in-naturals)])
               (values (var-x x) (parameter i)))])
      (append (eval e ρ empty)))))

(eval (CPS (P (λ (x) (if0 (flip 1/2) x 1)))))

#;(unP (CPS (P (λ (x) (if0 (flip 1/2) x 1)))))
#;'(true (result ℓ) (parameter 0))
#;'(fals (result ℓ) (degenerat 1))

(module+ test
'(λ (x k203) (flip 1/2 (λ (r204) (if0 r204 (k203 x) (k203 1))) ℓ201)) 
'(flip 1/2 (λ (r204) (if0 r204 (k203 x) (k203 1))) ℓ201) '((x . (parameter 0))) '(hole)
'(if0 r204 (k203 x) (k203 1)) '((x . (parameter 0)) (r204 . (result ℓ201))) '(hole)
'(k203 x) '((x . (parameter 0)) (r204 . (result ℓ201))) '(true (result ℓ201) '(hole))
'(true (result ℓ201) (parameter 0))
'(k203 1) '((x . (parameter 0)) (r204 . (result ℓ201))) '(fals (result ℓ201) (hole))
'(fals (result ℓ201) (degenerate 1)))
