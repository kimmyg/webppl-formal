#lang racket/base
(require racket/match
         math/distributions)

;; type-directed program generation

;; a program is a closed term, so we maintain a type environment. each candidate in the environment
;; has the same probability of being chosen as each compatible language construct has of being used.
;; this directs the generation process toward convergence.

;; types

(struct T () #:transparent)
(struct B T () #:transparent)
(struct R T () #:transparent)
(struct R+ T () #:transparent)
(struct P T () #:transparent)
(struct -> T (Ts T) #:transparent)

;; expression types
;; Γ |- true | false : B
;; Γ |- <real> : R
;; Γ |- <real> >= 0 : R+
;; Γ |- r : R+ ==> Γ |- r : R
;; Γ |- 0 <= <real> <= 1 : P
;; Γ |- p : P ==> Γ |- p : R+
;; x : S :: Γ |- e : T ==> Γ |- λx.e : S -> T for all types S and T
;; (and naturally extended to multi-argument functions)
;; Γ |- flip : P -> B
;; Γ |- beta : R+ R+ -> P
;; Γ |- gaussian : R R+ -> R
;; Γ |- + : R R -> R
;; Γ |- - : R R -> R
;; Γ |- * : R R -> R
;; Γ |- < : R R -> B
;; Γ |- <= : R R -> B
;; Γ |- > : R R -> B
;; Γ |- >= : R R -> B
;; Γ |- f : S -> T, Γ |- e : S ==> Γ |- f e : T (multi-argument in natural way)
;; Γ |- ec : B, Γ |- et : T, Γ |- ef : T ==> Γ |- if ec then et else ef : T for all types T
;; Γ |- e0 : S, x : S :: Γ |- e1 :: T ==> let x = e0 in e1 : T for all types T

;; (can/should we make * polymorphic?)
;; (can we add more general rules, like 1 - P : P for all P?)

;; the generation process should be covariant.
;; we ask for a term of type T and the process should consider all terms with type T' where T' <: T
;; (where <: is the subtype relation).
;; similarly, if we have type T in negative position, we accept all T' such that T' <: T.
;; the result is in the negative position, in a way.

(define (geometric p)
  (if (< (random) p) 0 (add1 (geometric p))))

(define <:
  (match-lambda**
   [((B) (B)) #t]
   [((R) (R)) #t]
   [((R+) (R+)) #t]
   [((P) (P)) #t]
   #;[((R+) (R)) #t]
   #;[((P) (R+)) #t]
   #;[((P) (R)) #t]
   [((-> Ds0 R0) (-> Ds1 R1))
    (and (= (length Ds0) (length Ds1))
         (andmap <: Ds1 Ds0)
         (<: R0 R1))]
   [(_ _) #f]))

(define (Γ-update x T Γ)
  (hash-update Γ T (λ (xs) (cons x xs)) null))

(define (Γ-update* xs Ts Γ)
  (foldl Γ-update Γ xs Ts))

(define (Γ-lookup Γ T0)
  (for/fold ([t #f]
             [i 1])
      ([(T ts) (in-hash Γ)])
    (if (<: T T0)
      (for/fold ([t0 t]
                 [i i])
          ([t (in-list ts)])
        (values (if (zero? (random i)) t t0) (add1 i)))
      (values t i))))

(define (make-fresh base)
  (let ([i 0]) (λ () (begin0 (string->symbol (format "~a~a" base i)) (set! i (add1 i))))))

(define (generate-program T)
  (define fresh-var (make-fresh 'x))
  (define fresh-lab (make-fresh 'ℓ))

  (define (generate-arrow-type T0 Γ)
    (let* ([Ts (for/fold ([Ts null])
                   ([(T ts) (in-hash Γ)])
                 (match T
                   [(-> _ (? (λ (T) (<: T T0))))
                    (for/fold ([Ts Ts])
                        ([t (in-list ts)])
                      (cons T Ts))]
                   [_ Ts]))]
           [i (random (add1 (length Ts)))])
      (if (< i (length Ts))
        (list-ref Ts i)
        (-> (for/list ([i (in-range (geometric 0.75))]) (generate-type Γ)) T0))))
  
  (define (generate-type Γ)
    (case (random 7)
      [(0 1 2) (B)]
      [(3 4 5) (R)]
      [(6) (generate-arrow-type (generate-type Γ) Γ)]))

  (define (generate-B) (not (zero? (sample (bernoulli-dist)))))
  (define (generate-P) (sample (uniform-dist)))
  (define (generate-R+) (sample (gamma-dist)))
  (define (generate-R) (sample (normal-dist)))

  (define (generate--> Ds R Γ)
    (let ([xs (for/list ([D (in-list Ds)]) (fresh-var))])
      `(λ ,xs ,(generate-term R (Γ-update* xs Ds Γ)))))
  
  (define (generate-application T Γ)
    (let ([->T (generate-arrow-type T Γ)])
      `(,(generate-term ->T Γ)
        ,@(for/list ([T (in-list (->-Ts ->T))]) (generate-term T Γ))
        ,(fresh-lab))))

  (define (generate-conditional T Γ)
    `(if ,(generate-term (B) Γ) ,(generate-term T Γ) ,(generate-term T Γ)))

  (define (generate-let T Γ)
    (let ([x (fresh-var)]
          [Tx (generate-type Γ)])
      `(let ([,x ,(generate-term Tx Γ)]) ,(generate-term T (Γ-update x Tx Γ)))))
  
  (define (generate-term T Γ)
    (let-values ([(t n) (Γ-lookup Γ T)])
      (if (and t #;(not (zero? (random n)))
               )
        t
        (case (random 8)
          [(1) (generate-application T Γ)]
          [(2) (generate-conditional T Γ)]
          [(3) (generate-let T Γ)]
          [else
           (match T
             [(B) (case (random 2)
                    [(0) (generate-B)]
                    [(1) `(flip ,(generate-term (P) Γ) ,(fresh-lab))])]
             [(R) (case (random 2)
                    [(0) (generate-R)]
                    [(1) `(gaussian ,(generate-term (R) Γ) ,(generate-term (R+) Γ) ,(fresh-lab))])]
             [(R+) (generate-R+)]
             [(P) (case (random 2)
                    [(0) (generate-P)]
                    [(1) `(beta ,(generate-term (R+) Γ) ,(generate-term (R+) Γ) ,(fresh-lab))])]
             [(-> Ds R) (generate--> Ds R Γ)])]))))

  (generate-term T (hash (-> (list (R) (R)) (R)) '(+ - *)
                         (-> (list (R) (R)) (B)) '(< <= > >=)
                         (-> (list (P)) (B)) '(flip flip flip)
                         (-> (list (R+) (R+)) (P)) '(beta beta beta)
                         (-> (list (R) (R+)) (R)) '(gaussian gaussian gaussian))))
