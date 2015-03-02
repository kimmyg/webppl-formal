#lang racket/base
(require racket/match
	 (for-syntax racket/base
		     racket/match))

(provide (all-defined-out))

(struct var (x) #:transparent)
(struct hvar var () #:transparent)
(struct svar var () #:transparent)

(struct exp () #:transparent)
(struct app exp (f es ℓ) #:transparent)
(struct lam exp (xs e) #:transparent)
(struct num exp (n) #:transparent)
(struct ref exp (x) #:transparent)
(struct href ref () #:transparent)
(struct sref ref () #:transparent)
(struct fix exp (x λ e) #:transparent)
(struct if0 exp (t c a) #:transparent)

(define (fresh-ℓ) (gensym 'ℓ))

(begin-for-syntax
 (define (in-ρ x ρ)
   (ormap (λ (y) (bound-identifier=? x y)) ρ))

 (define (E stx ρ)
   (syntax-case stx (λ fix if0)
     [(λ (xs ...) e)
      (andmap identifier? (syntax->list #'(xs ...)))
      (let-values ([(e hrefs) (E #'e (syntax->list #'(xs ...)))])
	(values #`(lam (list #,@(map (λ (x) (if (in-ρ x hrefs) #`(hvar '#,x) #`(svar '#,x))) (syntax->list #'(xs ...)))) #,e) hrefs))]
     #;
     [(fix x (λ (xs ...) e0) e1)
     (and (identifier? #'x) (andmap identifier? (syntax->list #'(xs ...))))
     (let-values ([(e0 e0-hrefs) (E #'e0 (cons #'x (syntax->list #'(xs ...))))]
     [(e1 e1-hrefs) (E #'e1 (cons #'x ρ))])
     (values #`(fix #,(if (in-ρ #'x (append e0-hrefs e1-hrefs)) #'(hvar 'x) #'(svar 'x))
     (lam (list #,@(map (λ (x) (if (in-ρ x hrefs) #`(hvar '#,x) #`(svar '#,x))) (syntax->list #'(xs ...)))) #,e) hrefs)))
     ]
     [(if0 t c a)
      (let-values ([(t t-hrefs) (E #'t ρ)]
		   [(c c-hrefs) (E #'c ρ)]
		   [(a a-hrefs) (E #'a ρ)])
	(values #`(if0 #,t #,c #,a) (append t-hrefs c-hrefs a-hrefs)))]
     [(f es ...)
      (let-values ([(f f-hrefs) (E #'f ρ)]
		   [(es es-hrefs)
		    (let loop ([es (syntax->list #'(es ...))])
		      (match es
			[(list)
			 (values null null)]
			[(cons e es)
			 (let-values ([(e e-hrefs) (E e ρ)]
				      [(es es-hrefs) (loop es)])
			   (values (cons e es) (append e-hrefs es-hrefs)))]))])
	(values #`(app #,f (list #,@es) (fresh-ℓ)) (append f-hrefs es-hrefs)))]
     [x
      (identifier? #'x)
      (if (in-ρ #'x ρ)
	  (values #'(sref 'x) null)
	  (values #'(href 'x) (list #'x)))]
     [n
      (number? (syntax->datum #'n))
      (values #'(num n) null)])))

(define-syntax (P stx)
  (syntax-case stx ()
    [(_ p)
     (let-values ([(p hvars) (E #'p null)])
       p)]))

(struct kvar svar () #:transparent)
(struct kref sref () #:transparent)

(struct ulam exp (xs k e) #:transparent)
(struct uapp exp (f es k ℓ) #:transparent)

(struct klam exp (x e) #:transparent)
(struct kapp exp (k e) #:transparent)

(define (CPS p)
  (define (bind k K)
    (cond
      [(klam? k)
       (let ([k0 (gensym 'k)])
	 (uapp (ulam null (kvar k0) (K (kref k0))) null k k0))]
      [(kref? k)
       (K k)]
      [else
       (error 'bind "unexpected k: ~a" k)]))
  (define (atomize e K)
    (cond
      [(or (num? e)
	   (ref? e))
       (K e)]  
      [(app? e)
       (let ([r (gensym 'r)])
	 (CPS e (klam (svar r) (K (sref r)))))]
      [(if0? e)
       (let ([t (gensym 't)])
	 (CPS e (klam (svar t) (K (sref t)))))]
      [else
       (match e
	 [(lam xs e)
	  (let ([k (gensym 'k)])
	    (K (ulam xs (kvar k) (CPS e (kref k)))))])]))
  (define (atomize* es K)
    (match es
      [(list)
       (K (list))]
      [(cons e es)
       (atomize e (λ (e) (atomize* es (λ (es) (K (cons e es))))))]))
  (define (CPS e k)
    (cond
      [(or (num? e)
	   (ref? e))
       (kapp k e)]
      [(lam? e)
       (atomize e (λ (e) (kapp k e)))]
      [else
       (match e
	[(app f es ℓ)
	 (atomize f (λ (f) (atomize* es (λ (es) (uapp f es k ℓ)))))]
	[(if0 t c a)
	 (bind k (λ (k) (atomize t (λ (t) (if0 t (CPS c k) (CPS a k))))))])]))
  (let ([k (gensym 'k)])
    (ulam null (kvar k) (CPS p (kref k)))) )

(define (unCPS e)
  e
  #;
  (if (or (num? e)
  (ref? e))
  e
  (match e
  [(uapp f es k ℓ)
  (match k
  [(kref k)
  (app (unCPS f) (map unCPS es) ℓ)]
  [(klam (svar r) e)])]
  [(kapp k e)
  (match k
  [(kref k)
  (unCPS e)])]
  [(ulam xs k e)
  (lam xs (unCPS e))])))

(define unP
  (match-lambda
    [(app f es ℓ)
     `(,(unP f) ,@(map unP es) ,ℓ)]
    [(lam xs e)
     `(λ ,(map unP xs) ,(unP e))]
    [(if0 t c a)
     `(if0 ,(unP t) ,(unP c) ,(unP a))]
    [(or (hvar x)
	 (svar x))
     x]
    [(num n) n]
    [(ref x) x]
    [(klam x e)
     `(λ (,(unP x)) ,(unP e))]
    [(kapp k e)
     `(,(unP k) ,(unP e))]
    [(uapp f es k ℓ)
     `(,(unP f) ,@(map unP es) ,(unP k) ,ℓ)]
    [(ulam xs k e)
     `(λ (,@(map unP xs) ,(unP k)) ,(unP e))]))

(module+ main
  (unP (CPS (P (f (g 42)))))
  (unP (CPS (P ((λ (x) (x x)) (λ (y) (y y))))))
  (unP (CPS (P (if0 0 5 6))))
  (unP (CPS (P (f (if0 0 5 6)))))
  (unP (CPS (P (f (if0 (g 42) 5 6))))))
