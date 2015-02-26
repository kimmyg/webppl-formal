#lang racket/base
(require racket/list
	 racket/match
	 "parse.rkt"
	 "eval.rkt"
	 "util.rkt")

(define (close v ve)
  (match v
    [(? number? n) n]
    [(cons λ β)
     (cons λ (for/hasheq ([(x t) (in-hash β)])
	       (values x (close (hash-ref ve (cons x t)) ve))))]))

(define (A ae β ve)
  (if (or (ulam? ae)
	  (klam? ae))
    (cons ae (restrict β (free-vars ae)))
    (match ae
      [(num n)
       n]
      [(or (href x)
	   (sref x))
       (hash-ref ve (cons x (hash-ref β x)))])))

(struct U/CEA (call β ve t))
(struct UAE (proc d c ve t))
(struct CAE (proc d ve t))

(define (=> ς ℓ)
  (match ς
    [(U/CEA (and φ (uapp f e q)) β ve t)
     (=> (UAE (A f β ve)
	      (A e β ve)
	      (A q β ve)
	      ve
	      (cons (ℓ φ) t))
	 ℓ)]
    [(U/CEA (and φ (kapp q e)) β ve t)
     (=> (CAE (A q β ve)
	      (A e β ve)
	      ve
	      (cons (ℓ φ) t))
	 ℓ)]
    [(UAE (cons (ulam u k call) β) d c ve t)
     (=> (U/CEA call
		(hash-set (hash-set β u t) k t)
		(hash-set (hash-set ve (cons u t) d) (cons k t) c)
		t)
	 ℓ)]
    [(UAE (cons (ulam u k call) β) d c ve t)
     (=> (U/CEA call
		(hash-set (hash-set β u t) k t)
		(hash-set (hash-set ve (cons u t) d) (cons k t) c)
		t)
	 ℓ)]
    [(CAE (cons (klam u call) β) d ve t)
     (=> (U/CEA call
		(hash-set β u t)
		(hash-set ve (cons u t) d)
		t)
	 ℓ)]
    [(CAE (cons #f β) d ve t)
     (close d ve)]))

(define (inject p x)
  (UAE (cons p (hasheq))
       x
       (cons #f (hasheq))
       (hash)
       empty))

(define (eval p x)
  (=> (inject p x) (make-ℓ p)))
