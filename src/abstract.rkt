#lang racket/base
(require racket/match
	 "parse.rkt"
	 "eval.rkt"
	 "util.rkt")

(define (Au e st h)
  (if (ulam? e)
    (seteq e)
    (match e
      [(href x)
       (hash-ref h x)]
      [(sref x)
       (hash-ref st x)])))

(struct U/CEA (call st h))
(struct UAE (proc d c st h))

(define =>
  (match-lambda
    [(U/CEA (uapp f e q) st h)
     (let ([d (Au e st h)]
	   [c (Ak q st)])
       (for/set ([λ (in-set (Au f st h))])
	 (let ([st′ (cond
		      [(kref? q) (pop st)]
		      [(or (href? f) (ulam? f)) st]
		      [else (stack-set st f (seteq))])])
	   (UAE λ d c st′ h))))]
    [(UAE (ulam (u k) call) d c st h)
     (let ([st′ (push (frame 'u d 'k c) st)]
	   []))]))
