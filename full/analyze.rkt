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

(struct immediate (e) #:transparent)
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
(struct ς-exit (σ v ω) #:transparent)
(struct ς-call (σ ρ Ω f es κ ℓ) #:transparent)
(struct ς-tail (σ ρ Ω f es ℓ) #:transparent)

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

(define empty-Ω (hasheq))

(define (Ω-update x ω Ω)
  (hash-set Ω (var-x x) ω))

(define (Ω-update* xs ωs Ω)
  (foldl Ω-update Ω xs ωs))

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
    (immediate e)
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

(define (ς-eval σ ρ Ω e)
  (match e
    [(or (uapp f es κ ℓ)
         (usam f es κ ℓ))
     (cond
       [(klam? κ)
        (list (ς-call σ ρ Ω f es κ ℓ))]
       [(kref? κ)
        (list (ς-tail σ ρ Ω f es ℓ))]
       [else
        (error 'ς-eval "unexpected κ: ~a" κ)])]
    [(kapp κ e)
     (let ([v (A e ρ σ)]
           [ωv (D e Ω)])
       (match κ
         [(klam x e)
          (ς-eval σ (ρ-update x v ρ) (Ω-update x ωv Ω) e)]
         [(kref κ)
          (list (ς-exit σ v 'oops))]))]
    [(if0 t c a)
     (let ([v (A t ρ σ)])
       (let* ([ςs null]
	      [ςs (if (or (set-member? v 0) (set-member? v 'num)) (append (ς-eval σ ρ Ω c) ςs) ςs)]
	      [ςs (if (or (set-member? v 1) (set-member? v 'num)) (append (ς-eval σ ρ Ω a) ςs) ςs)])
	 ςs))]))

(define succs
  (match-lambda
    [(ς-entr σ 'betaERP (list v0 v1))
     (list (ς-exit σ (set 'num) `(NODE ,(parameter 0) ,(parameter 1))))]
    [(ς-entr σ 'bernoulliERP (list v))
     (list (ς-exit σ (set 'num) `(NODE ,(parameter 0))))]
    [(ς-entr σ 'not (list v))
     (list (ς-exit σ (set #t #f) `(NODE ,(parameter 0))))]
    [(ς-entr σ 'zero? (list v))
     (list (ς-exit σ (set #t #f) `(NODE ,(parameter 0))))]
    [(ς-entr σ (ulam xs κ e) vs)
     (let ([ρ empty-ρ]
           [Ω empty-Ω])
       (let ([σ (σ-update* xs vs σ)]
	     [ρ (ρ-update* xs vs ρ)]
             [Ω (Ω-update* xs (build-list (length xs) parameter) Ω)])
	 (ς-eval σ ρ Ω e)))]
    [(or (ς-call σ ρ Ω f es _ _)
	 (ς-tail σ ρ Ω f es _))
     (let ([vs (map (λ (e) (A e ρ σ)) es)])
       (match f
	 [(href (and f (or 'betaERP 'bernoulliERP 'not 'zero?)))
	  (list (ς-entr σ f vs))]
	 [f
	  (for/list ([f (in-set (A f ρ σ))])
	    (ς-entr σ f vs))]))]))

(define (analyze p)
  (define (propagate seen work ς0 ς1)
    (let ([ς0×ς1 (cons ς0 ς1)])
      (if (set-member? seen ς0×ς1) work	(set-add work ς0×ς1))))
  
  (define (propagate* seen work ς0 ς1s)
    (foldl (λ (ς1 work) (propagate seen work ς0 ς1)) work ς1s))

  (define (update seen work ς0 ς1 ς2 ς3)
    (match-let ([(ς-call σ1 ρ1 Ω1 f1 es1 (klam x e) ℓ1) ς1]
		[(ς-entr σ2 f2 vs2) ς2]
		[(ς-exit σ3 v3 ω3) ς3])
      (let ([σ σ3]
	    [ρ ρ1]
            [Ω Ω1])
        ; fake-rebinding solution
        (let ([ρ (if (href? f1) (ρ-update (hvar (ref-x f1)) (set f2) ρ) ρ)])
          (let ([ρ (ρ-update x v3 ρ)]
                [Ω (Ω-update x (result ℓ1) Ω)])
            (propagate* seen work ς0 (ς-eval σ ρ Ω e)))))))
  
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
               [results (hash)]
	       [finals (set)])
      (match work
	[(list)
	 (values ς-init seen calls tails summaries results finals)]
	[(cons (and ς0×ς1 (cons ς0 ς1)) work)
	 (let ([seen (set-add seen ς0×ς1)])
	   (cond
	     [(ς-entr? ς1)
	      (let ([work (propagate* seen work ς0 (succs ς1))])
		(loop seen work calls tails summaries results finals))]
	     [(ς-call? ς1)
              (let ([ς2s (succs ς1)])
                (let-values ([(results) (foldl (λ (ς2 results)
                                                 (hash-update results ς0
                                                              (λ (->) (hash-update -> (ς-call-ℓ ς1) (add ς2) (set)))
                                                              (hasheq)))
                                               results ς2s)]
                             [(work calls) (call seen work calls summaries ς0×ς1 ς2s
                                                 (λ (work ς2 ς3) (update seen work ς0 ς1 ς2 ς3)))])
                  (loop seen work calls tails summaries results finals)))]
	     [(ς-tail? ς1)
              (let ([ς2s (succs ς1)])
                (let-values ([(results) (foldl (λ (ς2 results)
                                                 (hash-update results ς0
                                                              (λ (->) (hash-update -> (ς-tail-ℓ ς1) (add ς2) (set)))
                                                              (hasheq)))
                                               results ς2s)]
                             [(work tails) (call seen work tails summaries ς0×ς1 ς2s
                                                 (λ (work ς2 ς3) (propagate seen work ς0 ς3)))])
		(loop seen work calls tails summaries results finals)))]
	     [(ς-exit? ς1)
	      (if (equal? ς0 ς-init)
		(loop seen work calls tails summaries results (set-add finals ς1))
		(let ([summaries (hash-update summaries ς0 (add ς1) (set))])
		  (let* ([work (retr seen work calls ς0
				     (λ (work ς2 ς3) (update seen work ς2 ς3 ς0 ς1)))]
			 [work (retr seen work tails ς0
				     (λ (work ς2 ς3)
                                       (match-let ([(ς-exit σ1 v1 ω1) ς1]
                                                   [(ς-tail σ3 ρ3 Ω3 f3 es3 ℓ3) ς3])
                                         (let ([ω1 (match ω1
                                                     [`(NODE ,p0)
                                                      `(NODE ,(D (list-ref es3 0) Ω3))]
                                                     [`(NODE ,p0 ,p1)
                                                      `(NODE ,(D (list-ref es3 0) Ω3) ,(D (list-ref es3 1) Ω3))])])
                                           (propagate seen work ς2 (ς-exit σ1 v1 ω1))))))])
		    (loop seen work calls tails summaries results finals))))]
	     [else
	      (error 'analyze "unrecognized state ~a" ς1)]))]))))

(module+ main
  (define p0 (P ((λ (beta) ((λ (flip) (flip (beta 1 1)))
                            (λ (p) (not (zero? (sample bernoulliERP p))))))
                 (λ (α β) (sample betaERP α β)))))

  (displayln (unP p0))

  (define (sample-entries ςs)
    (for/fold ([ςs (set)])
        ([ς0 (in-set ςs)])
      (if (memq (ς-entr-f ς0) '(betaERP bernoulliERP))
        (set-add ςs ς0)
        ςs)))

  (define (resolve calls tails summaries results)
    (letrec ([inner0 (λ (ς0 s)
                      (match s
                        [`(NODE ,v0)
                         (inner1 ς0 v0)]
                        [`(NODE ,v0 ,v1)
                         (inner1 ς0 v0)]))]
             [inner1 (λ (ς0 v)
                       (match v
                           [(parameter 0)
                            (if (hash-has-key? calls ς0)
                              (match-let* ([(cons ς0 ς1) (set-first (hash-ref calls ς0))]
                                           [(ς-call σ1 ρ1 Ω1 f1 es1 k1 ℓ1) ς1])
                                (cons ℓ1 (inner1 ς0 (D (car es1) Ω1))))
                              (match-let* ([(cons ς0 ς1) (set-first (hash-ref tails ς0))]
                                           [(ς-tail σ1 ρ1 Ω1 f1 es1 ℓ1) ς1])
                                (cons ℓ1 (inner1 ς0 (D (car es1) Ω1)))))]
                           [(result ℓ) ; below returns summary entry states
                            (let ([ς0 (set-first (hash-ref (hash-ref results ς0) ℓ))])
                              (cons `(- ,ℓ) (inner0 ς0 (ς-exit-ω (set-first (hash-ref summaries ς0))))))]
                           [(immediate e)
                            e]))])
      inner0))
  
  (let-values ([(ς-init seen calls tails summaries results finals) (analyze (CPS p0))])
    (for ([ς0 (in-set (sample-entries (hash-keys summaries)))])
      (for ([ς1 (in-set (hash-ref summaries ς0))])
        ((current-print) ((resolve calls tails summaries results) ς0 (ς-exit-ω ς1)))))))

; delta address not as expected
; join delta addresses
; propagate blanket of conditional, more elaborate matching
; stop hardcoding the node resolution
; get it working with cycles
; get forward deltas working too
; formalize precision of forward and backward (can we just reverse the relation that we extract?)

