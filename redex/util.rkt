#lang racket/base
(require math/distributions)

(define (backflip x p) (not (zero? (inexact->exact (flbernoulli-inv-cdf p x #f #f)))))
(define (backbeta x α β) (flbeta-inv-cdf α β x #f #f))
(define (backgaussian x μ σ²) (flnormal-inv-cdf μ (sqrt σ²) x #f #f))

(define (->meta f)
  (case f
    [(+) +] [(-) -] [(*) *] [(/) /]
    [(=) =]
    [else (error '->meta "not defined for ~a" f)]))

(provide (all-defined-out))
