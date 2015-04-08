#lang racket/base
(require racket/match
         racket/set
         "parse.rkt")

(struct ς-entr (σ f vs) #:transparent)
(struct ς-call (σ ρ f es ℓ κ) #:transparent)
(struct ς-exit (σ v) #:transparent)

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

(define (inject p)
  (ς-entr empty-σ p null))

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

(define (ς-eval σ ρ e)
  (match e
    [(uapp f es κ ℓ)
     (list (ς-call σ ρ f es ℓ κ))]
    [(kapp κ e)
     (let ([v (A e ρ σ)])
       (match κ
         [(klam x e)
          (ς-eval σ (ρ-update x v ρ) e)]
         [(kref κ)
          (list (ς-exit σ v))]))]
    [(if0 t c a)
     (let ([v (A t ρ σ)])
       (let* ([ςs null]
	      [ςs (if (refines? 0 v) (append (ς-eval σ ρ c) ςs) ςs)]
	      [ςs (if (refines? 1 v) (append (ς-eval σ ρ a) ςs) ςs)])
	 ςs))]))

(define succs
  (match-lambda
    [(ς-entr σ (ulam xs κ e) vs)
     (let ([ρ empty-ρ])
       (let ([σ (σ-update* xs vs σ)]
	     [ρ (ρ-update* xs vs ρ)])
	 (ς-eval σ ρ e)))]
    [(ς-entr σ (and g (fix f (ulam xs κ e))) vs)
     (let ([ρ (ρ-update f (set g) empty-ρ)])
       (let ([σ (σ-update* xs vs σ)]
	     [ρ (ρ-update* xs vs ρ)])
	 (ς-eval σ ρ e)))]
    [(ς-call σ ρ f es _ _)
     (let ([vs (map (λ (e) (A e ρ σ)) es)])
       (for/list ([f (in-set (A f ρ σ))])
         (ς-entr σ f vs)))]))

(define (analyze p)
  (define (propagate work ς0 ς1)
    (cons (cons ς0 ς1) work))
  
  (define (propagate* work ς0 ς1s)
    (foldl (λ (ς1 work) (propagate work ς0 ς1)) work ς1s))

  (define (call work calls summaries ς0×ς1 ς2s)
    (match-let ([(cons ς0 ς1) ς0×ς1]
                [update (-update (-add ς0×ς1) (set))])
      (for/fold ([work work]
                 [calls calls])
          ([ς2 (in-list ς2s)])
        (values (for/fold ([work (propagate work ς2 ς2)])
                    ([ς3 (in-set (hash-ref summaries ς2 (set)))])
                  (retr* work ς0 ς1 ς2 ς3))
                (update ς2 calls)))))6
                

  (define (retr* work ς0 ς1 ς2 ς3)
    (match-let ([(ς-call σ1 ρ1 f1 es1 ℓ1 κ1) ς1])
      (match κ1
        [(klam x e)
         (match-let ([(ς-entr σ2 f2 vs2) ς2]
                     [(ς-exit σ3 v3) ς3])
           (let ([σ σ3]
                 [ρ ρ1]
                 [v v3])
             ; fake-rebinding on next line
            (let* ([ρ (if (href? f1) (ρ-update (hvar (ref-x f1)) (set f2) ρ) ρ)]
                   [ρ (ρ-update x v ρ)])
              (propagate* work ς0 (ς-eval σ ρ e)))))]
        [(kref κ)
         (propagate work ς0 ς3)])))
  
  (define (retr work calls summaries ς2 ς3)
    (values (for/fold ([work work])
                ([ς0×ς1 (in-set (hash-ref calls ς2 (set)))])
              (match-let ([(cons ς0 ς1) ς0×ς1])
                (retr* work ς0 ς1 ς2 ς3)))
            ((-update (-add ς3) (set)) ς2 summaries)))
  
  (let* ([ς0 (inject (CPS p))]
         [ς0×ς0 (cons ς0 ς0)])
    (let loop ([seen (set)]
               [work (list ς0×ς0)]
               [calls (hash)]
               [summaries (hash)])
      (match work
        [(list)
         (values calls summaries)]
        [(cons (and ς0×ς1 (cons ς0 ς1)) work)
         (if (set-member? seen ς0×ς1)
           (loop seen work calls summaries)
           (let ([seen (set-add seen ς0×ς1)])
             (cond
               [(ς-entr? ς1)
                (loop seen (propagate* work ς0 (succs ς1)) calls summaries)]
               [(ς-call? ς1)
                (let-values ([(work calls) (call work calls summaries ς0×ς1 (succs ς1))])
                  (loop seen work calls summaries))]
               [(ς-exit? ς1)
                (let-values ([(work summaries) (retr work calls summaries ς0 ς1)])
                  (loop seen work calls summaries))]
               [else
                (error 'analyze "unrecognized state ~a" ς1)])))]))))


(module+ main
  (define p0 (P 42))

  (define p1 (P ((λ (x) (x x)) (λ (y) (y y)))))

  (define p2 (P ((λ (x) (x x x)) (λ (y z) (y y z)))))
  
  (analyze p2))
  
  

  
