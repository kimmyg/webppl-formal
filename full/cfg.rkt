#lang racket/base
(require racket/match
         racket/set
         "parse.rkt")

(struct ς-entr (σ f vs) #:transparent)
(struct ς-call (σ ρ f es ℓ Ω H κ) #:transparent)
(struct ς-tail (σ ρ f es ℓ Ω H) #:transparent)
(struct ς-exit (σ v H ω) #:transparent)
(struct ς-retr ς-exit () #:transparent)

;; work and seen are pairs of states, compared for equality
;; once an entry state is made, it is reused


;; we relate-eq one exit state to many "predecessor" exit states
;; we relate one entry state to many exit states
;; we relate-eq one exit state to one (most recent) return state
;; we relate many return states to most recent return state
;; we relate many return states to entry

(struct result (ℓ) #:transparent)
(struct parameter (n) #:transparent)

(struct constant (e) #:transparent)
(struct random (xs) #:transparent)
(struct heapref (x) #:transparent)
(struct primitive (f xs) #:transparent)

(struct branch (ω) #:transparent)
(struct true branch () #:transparent)
(struct fals branch () #:transparent)

#;
(define (resolve ς ω)
  (match ω
    [(random ωs)
     (map (λ (ω) (resolve ς ωs)) ωs)]
    [(result ℓ)
     (let ([ς (let loop ([ς (hash-ref local-returns ς)])
                (if (equal? (ς-retr-ℓ ς) ℓ)
                    ς (loop (hash-ref local-returns ς))))])
       ()
       (resolve ς (ς-exit-ω ς)))]
    [(parameter n)
     (argument n)]))

(define empty-σ (hasheq))

(define (σ-update x v σ)
  (if (hvar? x)
    (hash-update σ (var-x x) (union v) (set))
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
  (if (or (ulam? e)
          (fix? e))
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
    (constant e)
    (match e
      [(href x)
       (heapref x)]
      [(sref x)
       (hash-ref Ω x)])))

(define (inject p)
  (ς-entr empty-σ p null))

(define ((-set v0) v1 h)
  (hash-set h v1 v0))

(define ((-update f v0) v1 h)
  (hash-update h v1 f v0))

(define ((-add v) s)
  (set-add s v))

(define ((union s1) s0)
  (set-union s0 s1))

(define (refines? v vα)
  (match v
    [0 (or (set-member? vα 0) (set-member? vα 'num))]
    [1 (or (set-member? vα 1) (set-member? vα 'num))]))

(define (ς-eval σ ρ e Ω H)
  (match e
    [(or (uapp f es κ ℓ)
         (usam f es κ ℓ))
     (cond
       [(klam? κ)
        (list (ς-call σ ρ f es ℓ Ω H κ))]
       [(kref? κ)
        (list (ς-tail σ ρ f es ℓ Ω H))]
       [else
        (error 'ς-eval "unexpected κ: ~a" κ)])]
    [(kapp κ e)
     (let ([v (A e ρ σ)]
           [ω (D e Ω)])
       (match κ
         [(klam x e)
          (ς-eval σ (ρ-update x v ρ) e (Ω-update x ω Ω) H)]
         [(kref κ)
          (list (ς-exit σ v H ω))]))]
    [(if0 t c a)
     (let ([v (A t ρ σ)]
           [ω (D t Ω)])
       (let* ([ςs null]
	      [ςs (if (refines? 0 v) (append (ς-eval σ ρ c Ω (cons (true ω) H)) ςs) ςs)]
	      [ςs (if (refines? 1 v) (append (ς-eval σ ρ a Ω (cons (fals ω) H)) ςs) ςs)])
	 ςs))]))

(define succs
  (match-lambda
    [(ς-entr σ 'betaERP (list v0 v1))
     (list (ς-exit σ null (set 'num) (random (list (parameter 0) (parameter 1)))))]
    [(ς-entr σ 'bernoulliERP (list v))
     (list (ς-exit σ null (set 'num) (random (list (parameter 0)))))]
    [(ς-entr σ 'not (list v))
     (list (ς-exit σ null (set #t #f) (primitive 'not (list (parameter 0)))))]
    [(ς-entr σ 'zero? (list v))
     (list (ς-exit σ null (set #t #f) (primitive 'zero? (list (parameter 0)))))]
    [(ς-entr σ (ulam xs κ e) vs)
     (let ([ρ empty-ρ]
           [Ω empty-Ω])
       (let ([σ (σ-update* xs vs σ)]
	     [ρ (ρ-update* xs vs ρ)]
             [Ω (Ω-update* xs (build-list (length xs) parameter) Ω)])
	 (ς-eval σ ρ e Ω null)))]
    [(ς-entr σ (and g (fix f (ulam xs κ e))) vs)
     (let ([ρ (ρ-update f (set g) empty-ρ)]
           [Ω (Ω-update f 'what?? empty-Ω)])
       (let ([σ (σ-update* xs vs σ)]
	     [ρ (ρ-update* xs vs ρ)]
             [Ω (Ω-update* xs (build-list (length xs) parameter) Ω)])
	 (ς-eval σ ρ e Ω null)))]
    [(or (ς-call σ ρ f es _ _ _ _)
	 (ς-tail σ ρ f es _ _ _))
     (let ([vs (map (λ (e) (A e ρ σ)) es)])
       (match f
	 [(href (and f (or 'betaERP 'bernoulliERP 'not 'zero?)))
	  (list (ς-entr σ f vs))]
	 [f
	  (for/list ([f (in-set (A f ρ σ))])
	    (ς-entr σ f vs))]))]))

(define (analyze p)
  (define (propagate work ς0 ς1)
    (cons (cons ς0 ς1) work))
  
  (define (propagate* work ς0 ς1s)
    (foldl (λ (ς1 work) (propagate work ς0 ς1)) work ς1s))

  (define (retr* work calls exits preds ς2 retr)
    (for/fold ([work work]
               [exits exits]
               [preds preds])
	([ς0×ς1 (in-set (hash-ref calls ς2 (set)))])
      (match-let ([(cons ς0 ς1) ς0×ς1])
	(retr work exits preds ς0 ς1))))  

  (define ((make-call-retr ς2 ς3) work exits preds ς0 ς1)
    (match-let ([(ς-call σ1 ρ1 f1 es1 ℓ1 Ω1 H1 (klam x e)) ς1]
                [(ς-entr σ2 f2 vs2) ς2]
                [(ς-exit σ3 v3 H3 ω3) ς3])
      (let ([σ σ3]
            [v v3]
            [H H1]
            [ω (result ℓ1)])
        (let ([ς* (ς-retr σ v H ω)])
          (let ([ρ ρ1]
                [Ω Ω1])
            ; fake-rebinding on next line
            (let ([ρ (if (href? f1) (ρ-update (hvar (ref-x f1)) (set f2) ρ) ρ)])
              (let ([ρ (ρ-update x v ρ)]
                    [Ω (Ω-update x ω Ω)])
                (let ([ς4s (ς-eval σ ρ e Ω H)])
                  (values (propagate* work ς0 ς4s)
                          ((-update (-add (cons ς2 ς3)) (set)) (cons ς0 ς*) exits)
                          (foldl (λ (ς4 preds) (hash-set preds (cons ς0 ς4) (list* ς* ς1 (hash-ref preds (cons ς0 ς1))))) preds ς4s))))))))))

  (define (call-retr work calls exits preds ς2 ς3)
    (retr* work calls exits preds ς2 (make-call-retr ς2 ς3)))

  (define ((make-tail-retr ς2 ς3) work exits preds ς0 ς1)
    (match-let ([(ς-tail σ1 ρ1 f1 es1 ℓ1 Ω1 H1) ς1]
                [(ς-exit σ3 v3 H3 ω3) ς3])
      (let ([ς4 (ς-exit σ3 v3 H1 (result ℓ1))])
        (values (propagate work ς0 ς4)
                ((-update (-add (cons ς2 ς3)) (set)) (cons ς0 ς4) exits) 
                (hash-set preds (cons ς0 ς4) (cons ς1 (hash-ref preds (cons ς0 ς1))))))))
  
  (define (tail-retr work tails exits preds ς2 ς3)
    (retr* work tails exits preds ς2 (make-tail-retr ς2 ς3)))

  (define (call* summaries work calls exits preds ς0×ς1 ς2s retr)
    (let ([update (-update (-add ς0×ς1) (set))])
      (for/fold ([work work]
                 [calls calls]
                 [exits exits]
                 [preds preds])
          ([ς2 (in-list ς2s)])
        (values (for/fold ([work (propagate work ς2 ς2)])
                          ([ς3 (in-set (hash-ref summaries ς2 (set)))])
                  (retr work ς2 ς3))
                (update ς2 calls)
                exits
                (hash-set preds (cons ς2 ς2) null)))))

  (define (call summaries work calls exits preds ς0×ς1 ς2s)
    (call* summaries work calls exits preds ς0×ς1 ς2s
           (match-let ([(cons ς0 ς1) ς0×ς1])
             (make-call-retr ς0 ς1))))
  
  (define (tail summaries work tails exits preds ς0×ς1 ς2s)
    (call* summaries work tails exits preds ς0×ς1 ς2s
           (match-let ([(cons ς0 ς1) ς0×ς1])
             (make-tail-retr ς0 ς1))))

  (let* ([ς0 (inject (CPS p))]
         [ς0×ς0 (cons ς0 ς0)])
    (let loop ([seen (set)]
               [work (list ς0×ς0)]
               [calls (hash)]
               [tails (hash)]
               [exits (hash)]
               [preds (hash-set (hash) ς0×ς0 null)]
               [summaries (hash)])
      (match work
        [(list)
         (values calls tails exits preds summaries)]
        [(cons (and ς0×ς1 (cons ς0 ς1)) work)
         (if (set-member? seen ς0×ς1)
             (loop seen work calls tails exits preds summaries)
             (let ([seen (set-add seen ς0×ς1)])
               (cond
                 [(ς-entr? ς1)
                  (let ([ς2s (succs ς1)])
                    (let ([work (propagate* work ς0 ς2s)]
                          [preds (foldl (λ (ς2 preds) (hash-set preds (cons ς0 ς2) (cons ς1 (hash-ref preds ς0×ς1)))) preds ς2s)])
                      (loop seen work calls tails exits preds summaries)))]
                 [(ς-call? ς1)
                  (let-values ([(work calls exits preds) (call summaries work calls exits preds ς0×ς1 (succs ς1))])
                    (loop seen work calls tails exits preds summaries))]
                 [(ς-tail? ς1)
                  (let-values ([(work tails exits preds) (tail summaries work tails exits preds ς0×ς1 (succs ς1))])
                    (loop seen work calls tails exits preds summaries))]
                 [(ς-exit? ς1)
                  (let ([summaries ((-update (-add ς1) (set)) ς0 summaries)])
                    (let*-values ([(work exits preds) (call-retr work calls exits preds ς0 ς1)]
                                  [(work exits preds) (tail-retr work tails exits preds ς0 ς1)])
                      (loop seen work calls tails exits preds summaries)))]
                 [else
                  (error 'analyze "unrecognized state ~a" ς1)])))])))
  )

(module+ main
  (define p0 (P 42))

  (define p1 (P (sample bernoulliERP (sample betaERP 1 1))))
  
  (define p2 (P ((λ (beta) ((λ (flip) (flip (beta 1 1)))
                            (λ (p) (not (zero? (sample bernoulliERP p))))))
                 (λ (α β) (sample betaERP α β)))))
 
  (define p3 (P ((λ (flip) ((λ (geom) (geom 1/2))
                            (fix geom (λ (p) (if (flip p) 0 (add1 (geom p)))))))
                 (λ (p) (not (zero? (sample bernoulliERP p)))))))
  
  (time (analyze p3)))
  
  

  
