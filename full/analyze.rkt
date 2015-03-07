#lang racket/base
(require #;(for-syntax racket/base)
         racket/match #;(rename-in racket/match [match rkt:match])
	 racket/set
	 "parse.rkt")

;; sinks

(struct returned () #:transparent)

(struct argument (ℓ) #:transparent)
(struct operator argument () #:transparent)
(struct operand argument (n) #:transparent)

;; sources

(struct immediate () #:transparent)
(struct parameter (n) #:transparent)
(struct result (ℓ) #:transparent)


;; sources are function parameters and the results of calls
;; sources are the things that have influence defined for them
;; in CPS, each of these are named via binding
;; the influence of the result of a call is a callsite label which serves to identify
;; both the contribution to the address and the syntactic call from which the result comes
;; sources are mapped in the influence environment to parameters and labels

;; sinks are function /arguments/ and returns
;; a function argument sink has a callsite label and argument position
;; this is a higher-order language, so the argument position might be operator

#;
(define-syntax (match stx)
  (syntax-case stx ()
    [(_ e clauses ...)
     (with-syntax ([line (syntax-line stx)])
       #'(begin
           (printf "~a ~a\n" '(match e) line)
           (rkt:match e clauses ...)))]))

;; the use environment has a map of labels to callsites and argument positions
;; the callsites include continuation calls
;; this means continuation callsites need labels too, but they won't be used as addresses
;; the result is a set of sources which can be parameters or the result of calls
  
(struct ς-entr (σ f vs) #:transparent)
(struct ς-exit (σ U v ω) #:transparent)
(struct ς-call (σ ρ xs U Ω f es ω k ℓ) #:transparent)
(struct ς-tail (σ ρ xs U Ω f es ω ℓ) #:transparent)

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
    (set (immediate))
    (match e
      [(href x)
       (set 'heap-ref-what-to-do)]
      [(sref x)
       (hash-ref Ω x)])))

(define (inject p)
  (ς-entr empty-σ p null))

(define ((add x) s)
  (set-add s x))

(define ((union s1) s0)
  (set-union s0 s1))

(define (ς-eval σ ρ xs U Ω e ω)
  (match e
    [(uapp f es k ℓ)
     (let ([U (for/fold ([U (if (sref? f) (hash-update U (ref-x f) (add (operator ℓ)) (set)) U)])
                  ([e (in-list es)]
                   [i (in-naturals)])
                 (if (sref? e)
                   (hash-update U (ref-x e) (add (operand ℓ i)) (set))
                   U))])
       (cond
         [(klam? k)
          (list (ς-call σ ρ xs U Ω f es ω k ℓ))]
         [(kref? k)
          (list (ς-tail σ ρ xs U Ω f es ω ℓ))]
         [else
          (error 'ς-eval "unexpected k: ~a" k)]))]
    [(kapp k e)
     (let ([v (A e ρ σ)]
           [ωv (D e Ω)])
       (match k
	 [(klam x e)
	  (ς-eval σ (ρ-update x v ρ) (hash-set Ω x ωv) e (set))]
	 [(kref k)
          (let* ([U (if (sref? e) (hash-update U (ref-x e) (add (returned)) (set)) U)]
                 [U (for/list ([x (in-list xs)])
                             (hash-ref U (var-x x) (set)))])
            (list (ς-exit σ U v (set-union ω ωv))))]))]
    [(if0 t c a)
     (let ([U (if (sref? t) (hash-update U (ref-x t) (add (immediate)) (set)) U)]
           [v (A t ρ σ)]
           [ωv (D t Ω)])
       (let* ([ςs null]
	      [ςs (if (or (set-member? v 0) (set-member? v 'num)) (append (ς-eval σ ρ xs U Ω c (set-union ω ωv)) ςs) ςs)]
	      [ςs (if (or (set-member? v 1) (set-member? v 'num)) (append (ς-eval σ ρ xs U Ω a (set-union ω ωv)) ςs) ςs)])
	 ςs))]))

(define succs
  (match-lambda
    [(ς-entr σ 'add1 (list v))
     (list (ς-exit σ (list (set (immediate))) (set 'num) (set `(Δ ()))))]
    [(ς-entr σ 'beta (list v0 v1))
     (list (ς-exit σ (list (set (immediate)) (set (immediate))) (set 'num) (set (immediate))))]
    [(ς-entr σ 'flip (list v))
     (list (ς-exit σ (list (set (immediate))) (set 'num) (set (immediate))))]
    [(ς-entr σ (ulam xs k e) vs)
     (let ([ρ empty-ρ]
           [Ω (for/hasheq ([x (in-list xs)]
                           [i (in-naturals)])
                (values (var-x x) (set (parameter i))))])
       (let ([σ (σ-update* xs vs σ)]
	     [ρ (ρ-update* xs vs ρ)])
	 (ς-eval σ ρ xs (hasheq) Ω e (set))))]
    [(or (ς-call σ ρ xs U Ω f es ω _ _)
	 (ς-tail σ ρ xs U Ω f es ω _))
     (let ([vs (map (λ (e) (A e ρ σ)) es)])
       (match f
	 [(href 'add1)
	  (list (ς-entr σ 'add1 vs))]
         [(href 'beta)
          (list (ς-entr σ 'beta vs))]
	 [(href 'flip)
	  (list (ς-entr σ 'flip vs))]
	 [_
	  (for/list ([f (in-set (A f ρ σ))])
	    (ς-entr σ f vs))]))]))

#;
(define (resolve* ω es Ω ℓ)
  (for/set ([d (in-set ω)])
    (resolve d es Ω ℓ)))

#;
  (define (resolve d es Ω ℓ)
    (if (num? d)
        '(Δ ())
        (match d
          [`(param ,n)
           (resolve (list-ref es n) es Ω ℓ)]
          [`(Δ ,ℓs)
           `(Δ ,(cons ℓ ℓs))]
          [(sref x)
           (hash-ref Ω x)])))

(define (analyze p)
  (define (propagate seen work ς0 ς1)
    (let ([ς0×ς1 (cons ς0 ς1)])
      (if (set-member? seen ς0×ς1) work	(set-add work ς0×ς1))))
  
  (define (propagate* seen work ς0 ς1s)
    (foldl (λ (ς1 work) (propagate seen work ς0 ς1)) work ς1s))

  (define (update seen work ς0 ς1 ς2 ς3)
    (match-let ([(ς-call σ1 ρ1 xs1 U1 Ω1 f1 es1 ω1 (klam x e) ℓ1) ς1]
		[(ς-entr σ2 f2 vs2) ς2]
		[(ς-exit σ3 U3 v3 ω3) ς3])
      (let ([σ σ3]
	    [ρ ρ1]
            [xs xs1]
            [U U1]
            [Ω Ω1])
        ; fake-rebinding solution
        (let ([ρ (if (href? f1) (ρ-update (hvar (ref-x f1)) (set f2) ρ) ρ)])
          (let ([ρ (ρ-update x v3 ρ)]
                [Ω (hash-set Ω (var-x x) (set (result ℓ1)))]) ; XXX TODO include the influence of the operator
            (propagate* seen work ς0 (ς-eval σ ρ xs U Ω e ω1)))))))
  
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
  (define (watch summaries)
    (for ([(ς ςs) (in-hash summaries)])
      (let ([f (ς-entr-f ς)])
        ((current-print) (if (symbol? f) f (unP f))))
      ((current-print)
       (for/fold ([summary (for/list ([v (in-list (ς-entr-vs ς))])
                             (set))])
                 ([ς (in-set ςs)])
         (for/list ([si (in-list summary)]
                    [ti (in-list (ς-exit-U ς))])
           (set-union si ti))))
      ((current-print)
       (for/fold ([summary (set)])
                 ([ς (in-set ςs)])
         (set-union summary (ς-exit-ω ς))))))
  
  #;(analyze (CPS (P ((λ (x) (x x)) (λ (y) (y y))))))
  (displayln "p")
  (let-values ([(ς-init seen calls tails summaries finals) (analyze (CPS (P ((λ (x) x) ((λ (y) y) 42)))))])
    (watch summaries))

  (displayln "p")
  (let-values ([(ς-init seen calls tails summaries finals) (analyze (CPS (P ((λ (z x) x) 34 ((λ (y) y) 42)))))])
    (watch summaries))
  
  (displayln "p")
  (let-values ([(ς-init seen calls tails summaries finals) (analyze (CPS (P ((λ () ((λ () 42)))))))])
    (watch summaries))

  (displayln "p")
  (let-values ([(ς-init seen calls tails summaries finals) (analyze (CPS (P (flip (beta 1 1)))))])
    (watch summaries))
  
  (displayln "p")
  (let-values ([(ς-init seen calls tails summaries finals) (analyze (CPS (P ((λ (x y) (if0 (flip 1/2) x y)) 12 13))))])
    (watch summaries)))
