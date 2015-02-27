#lang racket/base
(require racket/match
	 racket/set
	 "parse.rkt")

(struct ς-entr (σ f vs) #:transparent)
(struct ς-exit (σ v) #:transparent)
(struct ς-call (σ ρ f es k ℓ) #:transparent)
(struct ς-tail (σ ρ f es ℓ) #:transparent)

(define empty-σ (hasheq))

(define (σ-update x v σ)
  (if (hvar? x)
    (hash-update σ (var-x x) (λ (vs) (set-union vs v)) (set))
    σ))

(define (σ-update* xs vs σ)
  (foldl σ-update σ xs vs))

(define empty-ρ (hasheq))

(define (ρ-update x v ρ)
  (hash-set ρ (var-x x) v))

(define (ρ-update* xs vs ρ)
  (foldl ρ-update ρ xs vs))

(define (A e ρ σ)
  (if (ulam? e)
    (set e)
    (match e
      [(num n)
       (set n)]
      [(href x)
       (hash-ref σ x)]
      [(sref x)
       (hash-ref ρ x)])))

(define (inject p)
  (ς-entr empty-σ p null))

(define (ς-eval σ ρ e)
  (match e
    [(uapp f es k ℓ)
     (cond
       [(klam? k)
	(list (ς-call σ ρ f es k ℓ))]
       [(kref? k)
	(list (ς-tail σ ρ f es ℓ))]
       [else
	(error 'ς-eval "unexpected k: ~a" k)])]
    [(kapp k e)
     (let ([v (A e ρ σ)])
       (match k
	 [(klam x e)
	  (ς-eval σ (ρ-update x v ρ) e)]
	 [(kref k)
	  (list (ς-exit σ v))]))]
    [(if0 t c a)
     (let ([v (A t ρ σ)])
       (let* ([ςs null]
	      [ςs (if (or (set-member? v 0) (set-member? v 'num)) (append (ς-eval σ ρ c) ςs) ςs)]
	      [ςs (if (or (set-member? v 1) (set-member? v 'num)) (append (ς-eval σ ρ a) ςs) ςs)])
	 ςs))]))

(define succs
  (match-lambda
    [(ς-entr σ 'flip (list))
     (list (ς-exit σ (set 'num)))]
    [(ς-entr σ 'add1 (list v))
     (list (ς-exit σ (set 'num)))]
    [(ς-entr σ (ulam xs k e) vs)
     (let ([ρ empty-ρ])
       (let ([σ (σ-update* xs vs σ)]
	     [ρ (ρ-update* xs vs ρ)])
	 (ς-eval σ ρ e)))]
    [(or (ς-call σ ρ f es _ _)
	 (ς-tail σ ρ f es _))
     (let ([vs (map (λ (e) (A e ρ σ)) es)])
       (match f
	 [(href 'add1)
	  (list (ς-entr σ 'add1 vs))]
	 [(href 'flip)
	  (list (ς-entr σ 'flip vs))]
	 [_
	  (for/list ([f (in-set (A f ρ σ))])
	    (ς-entr σ f vs))]))]))

(define (analyze p)
  (define (propagate seen work ς0 ς1)
    (let ([ς0×ς1 (cons ς0 ς1)])
      (if (set-member? seen ς0×ς1) work	(set-add work ς0×ς1))))
  
  (define (propagate* seen work ς0 ς1s)
    (foldl (λ (ς1 work) (propagate seen work ς0 ς1)) work ς1s))

  (define (update seen work ς0 ς1 ς2 ς3)
    (match-let ([(ς-call σ1 ρ1 f1 es1 (klam x e) ℓ1) ς1]
		[(ς-entr σ2 f2 vs2) ς2]
		[(ς-exit σ3 v3) ς3])
      (let ([σ σ3]
	    [ρ ρ1])
	(let* ([ρ (if (href? f1) (ρ-update (hvar (ref-x f1)) (set f2) ρ) ρ)]
	       [ρ (ρ-update x v3 ρ)])
	  (propagate* seen work ς0 (ς-eval σ ρ e))))))
  
  (define (call seen work calls summaries ς0×ς1 ς2s f)
    (for/fold ([work work]
	       [calls calls])
	([ς2 (in-list ς2s)])
      (if (hash-has-key? summaries ς2)
	(values (for/fold ([work work])
		    ([ς3 (in-set (hash-ref summaries ς2))])
		  (f work ς2 ς3))
		calls)
	(let ([work (propagate seen work ς2 ς2)]
	      [calls (hash-update calls ς2 (λ (cs) (set-add cs ς0×ς1)) (set))])
	  (values work calls)))))
  
  (define (retr seen work calls ς0 f)
    (for/fold ([work work])
	([ς2×ς3 (in-set (hash-ref calls ς0 (set)))])
      (match-let ([(cons ς2 ς3) ς2×ς3])
	(f work ς2 ς3))))
  
  (let ([ς-init (inject p)])
    (let loop ([seen (set)]
	       [work (list (cons ς-init ς-init))]
	       [calls (hash)]
	       [tails (hash)]
	       [summaries (hash)]
	       [finals (set)])
      (match work
	[(list)
	 (values calls tails summaries finals)]
	[(cons (and ς0×ς1 (cons ς0 ς1)) work)
	 (let ([seen (set-add seen ς0×ς1)])
	   (cond
	     [(ς-entr? ς1)
	      (let ([work (propagate* seen work ς0 (succs ς1))])
		(loop seen work calls tails summaries finals))]
	     [(ς-call? ς1)
	      (let-values ([(work calls) (call seen work calls summaries ς0×ς1 (succs ς1)
					       (λ (work ς2 ς3) (update seen work ς0 ς1 ς2 ς3)))])
		(loop seen work calls tails summaries finals))]
	     [(ς-tail? ς1)
	      (let-values ([(work tails) (call seen work tails summaries ς0×ς1 (succs ς1)
					       (λ (work ς2 ς3) (propagate seen work ς0 ς3)))])
		(loop seen work calls tails summaries finals))]
	     [(ς-exit? ς1)
	      (if (equal? ς0 ς-init)
		(loop seen work calls tails summaries (set-add finals ς1))
		(let ([summaries (hash-update summaries ς0 (λ (ss) (set-add ss ς1)) (set))])
		  (let* ([work (retr seen work calls ς0
				     (λ (work ς2 ς3) (update seen work ς2 ς3 ς0 ς1)))]
			 [work (retr seen work tails ς0
				     (λ (work ς2 ς3) (propagate seen work ς2 ς1)))])
		    (loop seen work calls tails summaries finals))))]
	     [else
	      (error 'analyze "unrecognized state ~a" ς1)]))]))))

#;(define p (CPS (P ((λ (x) ((λ (y) (f y)) x)) ((λ () ((λ () 35))))))))

(define p (CPS (P ((λ (Y)
		     ((λ (geom)	(geom))
		      (Y (λ (geom) (λ () (if0 (flip) 0 (add1 (geom))))))))
		   (λ (f) ((λ (g0) (g0 g0))
			   (λ (f0) (λ () ((f (f0 f0)))))))))))

(let-values ([(calls tails summaries finals) (analyze p)])
  (displayln (map ς-exit-v (set->list finals)))
  #;
  (define consumption-point
  (car
  (filter
  (λ (ς) (eq? (ς-entr-f ς) 'const))
  (hash-keys summaries))))
  #;(displayln consumption-point)
  #;
  (match-let ([(cons entr tail) (set-first (hash-ref tails consumption-point))])
  (values entr tail)) )



#;
(module+ main
  (analyze (CPS (P ((λ (x) (x x)) (λ (y) (y y))))))
  (analyze (CPS (P ((λ (x) x) ((λ (y) y) 42))))))
