#lang racket
(require "parse.rkt")

(define (analyze p x)
  (match p))

(module+ main
  (analyze (P (λ (x k) (k x))) 42))
