#lang racket/base
(require racket/match
         redex
         (prefix-in dir: "direct.rkt")
         (prefix-in cps: "cps.rkt"))

(define (cps p)
  (define fresh-k
    (let ([k 0]) (λ () (begin0 (string->symbol (format "k~a" k)) (set! k (add1 k))))))
  (define fresh-x
    (let ([x 0]) (λ () (begin0 (string->symbol (format "x~a" x)) (set! x (add1 x))))))
  (define (atomize e F)
    (cond
      [(or (boolean? e)
           (number? e)
           (symbol? e))
       (F e)]
      [else (match e
              [`(fix ,x ,e)
               (atomize e (λ (e) (F `(fix ,x ,e))))]
              [`(λ ,xs ,e)
               (let ([k (fresh-k)])
                 (F `(λ ,(append xs (list k)) ,(cps e k))))]
              [`(,f ,es ... ,ℓ)
               (let ([x (fresh-x)])
                 (cps e `(μ (,x) ,(F x))))])]))
  (define (atomize* es F)
    (match es
      [(list) (F es)]
      [(cons e es)
       (atomize e (λ (e) (atomize* es (λ (es) (F (cons e es))))))]))
  (define (cps e κ)
    (cond
      [(or (boolean? e)
           (number? e)
           (symbol? e))
       `(,κ ,e)]
      [(eq? (car e) 'λ)
       (atomize e (λ (e) `(,κ ,e)))]
      [else (match e
              [`(fix ,x ,e)
               (atomize e (λ (e) `(,κ (fix ,x ,e))))]
              [`(if ,et ,ec ,ea)
               (atomize et (λ (et) `(if ,et ,(cps ec κ) ,(cps ea κ))))]
              [`(let ([,x0 ,e0]) ,e1)
               (cps `((λ (,x0) ,e1) ,e0 ℓ-let) κ)]
              [`(,f ,es ... ,ℓ)
               (atomize f (λ (f) (atomize* es (λ (es) (append (list f) es (list κ ℓ))))))]
              [e (error 'cps "no clause for ~a" e)])]))
  (let ([k (fresh-k)])
    `(λ (,k) ,(cps p k))))

(define (oracle ι) 0.5)

(define dir:-> (dir:make-> oracle))
(define cps:-> (cps:make-> oracle))

(define (test p)
  ((current-print) (apply-reduction-relation* dir:-> (term (dir:inject ,p))))
  ((current-print) (apply-reduction-relation* cps:-> (term (cps:inject ,(cps p))))))

(define (test2 p)
  ((current-print) p)
  ((current-print) (apply-reduction-relation* dir:-> (term (dir:inject ,p)))))

(require "generate.rkt")

(let loop ()
  (test2 (random-boolean-valued-program))
  (loop))


