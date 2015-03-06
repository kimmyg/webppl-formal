#lang racket/base
(require #;(for-syntax racket/base)
         racket/match #;(rename-in racket/match [match rkt:match])
	 racket/set
	 "parse.rkt")


#;
(define-syntax (match stx)
  (syntax-case stx ()
    [(_ e clauses ...)
     (with-syntax ([line (syntax-line stx)])
       #'(begin
           (printf "~a ~a\n" '(match e) line)
           (rkt:match e clauses ...)))]))

(struct ς-entr (σ f vs) #:transparent)
(struct ς-exit (σ v ω) #:transparent)
(struct ς-call (σ ρ Ω f es ω k ℓ) #:transparent)
(struct ς-tail (σ ρ Ω f es ω ℓ) #:transparent)

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

(define (D e Ω)
  (if (or (ulam? e)
          (num? e))
    (set (list))
    (match e
      [(href x)
       (set 'heap-ref-what-to-do)]
      [(sref x)
       (hash-ref Ω x)])))

(define (inject p)
  (ς-entr empty-σ p null))

(define ((union s1) s0)
  (set-union s0 s1))

(define (ς-eval σ ρ Ω e ω)
  (match e
    [(uapp f es k ℓ)
     (cond
       [(klam? k)
	(list (ς-call σ ρ Ω f es ω k ℓ))]
       [(kref? k)
	(list (ς-tail σ ρ Ω f es ω ℓ))]
       [else
	(error 'ς-eval "unexpected k: ~a" k)])]
    [(kapp k e)
     (let ([v (A e ρ σ)]
           [ω (D e Ω)])
       (match k
	 [(klam x e)
	  (ς-eval σ (ρ-update x v ρ) (hash-set Ω x ω) e (set))]
	 [(kref k)
	  (list (ς-exit σ v ω))]))]
    [(if0 t c a)
     (let ([v (A t ρ σ)]
           [ωv (D t Ω)])
       (let* ([ςs null]
	      [ςs (if (or (set-member? v 0) (set-member? v 'num)) (append (ς-eval σ ρ Ω c (set-union ω ωv)) ςs) ςs)]
	      [ςs (if (or (set-member? v 1) (set-member? v 'num)) (append (ς-eval σ ρ Ω a (set-union ω ωv)) ςs) ςs)])
	 ςs))]))

(define succs
  (match-lambda
    [(ς-entr σ 'flip (list))
     (list (ς-exit σ (set 'num)))]
    [(ς-entr σ 'add1 (list v))
     (list (ς-exit σ (set 'num)))]
    [(ς-entr σ (ulam xs k e) vs)
     (let ([ρ empty-ρ]
           [Ω (for/hasheq ([x (in-list xs)]
                           [i (in-naturals)])
                (values (var-x x) `(param ,i)))])
       (let ([σ (σ-update* xs vs σ)]
	     [ρ (ρ-update* xs vs ρ)])
	 (ς-eval σ ρ Ω e (set))))]
    [(or (ς-call σ ρ Ω f es ω _ _)
	 (ς-tail σ ρ Ω f es ω _))
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
    (match-let ([(ς-call σ1 ρ1 Ω1 f1 es1 ω1 (klam x e) ℓ1) ς1]
		[(ς-entr σ2 f2 vs2) ς2]
		[(ς-exit σ3 v3 ω3) ς3])
      #;(displayln Ω1)
      #;(displayln ω3)
      (let ([σ σ3]
	    [ρ ρ1]
            [Ω Ω1])
        ; fake-rebinding solution
        (let ([ρ (if (href? f1) (ρ-update (hvar (ref-x f1)) (set f2) ρ) ρ)])
          (let ([ρ (ρ-update x v3 ρ)]
                [Ω (hash-set Ω x ω3)]) ; XXX TODO include the influence of the operator
            (propagate* seen work ς0 (ς-eval σ ρ Ω e ω1)))))))
  
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
	 (values ς-init seen calls tails summaries finals)]
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

(module+ main
  (analyze (CPS (P ((λ (x) (x x)) (λ (y) (y y))))))
  (analyze (CPS (P ((λ (x) x) ((λ (y) y) 42))))))
