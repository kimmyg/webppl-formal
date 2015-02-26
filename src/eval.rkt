#lang racket/base
(require racket/match
	 racket/set
	 "parse.rkt")

(provide (all-defined-out))

(define free-vars
  (match-lambda
    [(num n) (seteq)]
    [(or (href x)
	 (sref x))
     (seteq x)]
    [(ulam x k e)
     (set-remove (set-remove (free-vars e) x) k)]
    [(uapp f e k)
     (set-union (free-vars f)
		(free-vars e)
		(free-vars k))]
    [(klam x e)
     (set-remove (free-vars e) x)]
    [(kapp k e)
     (set-union (free-vars k)
		(free-vars e))]))

(define (restrict β xs)
  (for/hasheq ([x (in-set xs)])
    (values x (hash-ref β x))))
