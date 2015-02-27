#lang racket/base
(require racket/match
	 (for-syntax racket/base
		     racket/match))

(provide (all-defined-out))

(struct var (x) #:transparent)
(struct hvar var () #:transparent)
(struct svar var () #:transparent)

(struct exp () #:transparent)
(struct app exp (f es) #:transparent)
(struct lam exp (xs e) #:transparent)
(struct num exp (n) #:transparent)
(struct ref exp (x) #:transparent)
(struct href ref () #:transparent)
(struct sref ref () #:transparent)

(begin-for-syntax
 (define (in-ρ x ρ)
   (ormap (λ (y) (bound-identifier=? x y)) ρ))

 (define (E stx ρ)
   (syntax-case stx (λ)
     [(λ (xs ...) e)
      (andmap identifier? (syntax->list #'(xs ...)))
      (let-values ([(e hrefs) (E #'e (syntax->list #'(xs ...)))])
	(values #`(lam (list #,@(map (λ (x) (if (in-ρ x hrefs) #`(hvar '#,x) #`(svar '#,x))) (syntax->list #'(xs ...)))) #,e) hrefs))]
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
	(values #`(app #,f (list #,@es)) (append f-hrefs es-hrefs)))]
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
(struct uapp exp (f es k) #:transparent)

(struct klam exp (x e) #:transparent)
(struct kapp exp (k e) #:transparent)

(define (CPS p)
  (define (atomize e K)
    (cond
      [(or (num? e)
	   (ref? e))
       (K e)]  
      [(app? e)
       (let ([r (gensym 'r)])
	 (CPS e (klam (svar r) (K (sref r)))))]
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
    (if (ref? e)
      (kapp k e)
      (match e
	[(app f es)
	 (atomize f (λ (f) (atomize* es (λ (es) (uapp f es k)))))])))
  (let ([k (gensym 'k)])
    (ulam null (kvar k) (CPS p (kref k)))) )

(define unP
  (match-lambda
    [(app f es)
     `(,(unP f) ,@(map unP es))]
    [(lam xs e)
     `(λ ,(map unP xs) ,(unP e))]
    [(or (hvar x)
	 (svar x))
     x]
    [(num n) n]
    [(ref x) x]
    [(klam x e)
     `(λ (,(unP x)) ,(unP e))]
    [(kapp k e)
     `(,(unP k) ,(unP e))]
    [(uapp f es k)
     `(,(unP f) ,@(map unP es) ,(unP k))]
    [(ulam xs k e)
     `(λ (,@(map unP xs) ,(unP k)) ,(unP e))]))

(module+ main
  (unP (CPS (P (f (g 42)))))
  (unP (CPS (P ((λ (x) (x x)) (λ (y) (y y)))))))
