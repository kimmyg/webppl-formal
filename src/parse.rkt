#lang racket/base
(require racket/match
	 (except-in (for-syntax racket/base) =>))

(provide (all-defined-out))

(struct num (n))

(struct hvar (x))
(struct svar (x))
(struct kvar svar ())

(struct href (x))
(struct sref (x))
(struct kref sref ())

(struct ulam (x k e))
(struct uapp (f e k))

(struct klam (x e))
(struct kapp (k e))

(begin-for-syntax
 (define-syntax-rule (=> e0 e1)
   (or (not e0) e1))

 (define (in-ρ x ρ)
   (ormap (λ (y) (bound-identifier=? x y)) ρ))
 
 (define (parse-aexp stx ρ u κ)
   (syntax-case stx (λ)
     [(λ (x k) e)
      (not (bound-identifier=? #'x #'k))
      (let-values ([(e hrefs) (parse-call #'e (cons #'x (remove #'k ρ)) #'x #'k)])
	(values #`(ulam #,(if (in-ρ #'x hrefs) #'(hvar 'x) #'(svar 'x)) (kvar 'k) #,e) hrefs))]
     [x
      (=> (identifier? #'x) (not (bound-identifier=? #'x κ)))
      (cond
        [(and (identifier? #'x) (bound-identifier=? #'x u))
	 (values #'(sref 'x) null)]
	[(and (identifier? #'x) (in-ρ #'x ρ))
	 (values #'(href 'x) (list #'x))]
	[(number? (syntax->datum #'x))
	 (values #'(num x) null)]
	[else
	 (raise-syntax-error #f "expected bound identifier or number" #'x)])]))

 (define (parse-cont stx ρ u κ)
   (syntax-case stx (λ)
     [(λ (x) e)
      (not (bound-identifier=? #'x κ))
      (let-values ([(e hrefs) (parse-call #'e (cons #'x ρ) u κ)])
	(values #`(klam (svar 'x) #,e) hrefs))]
     [x
      (and (identifier? #'x) (bound-identifier=? #'x κ))
      (values #'(kref 'x) null)]))
 
 (define (parse-call stx ρ u κ)
   (syntax-case stx ()
     [(k e)
      (let-values ([(k k-hrefs) (parse-cont #'k ρ u κ)]
		   [(e e-hrefs) (parse-aexp #'e ρ u κ)])
	(values #`(kapp #,k #,e)
		(append k-hrefs e-hrefs)))]
     [(f e k)
      (let-values ([(f f-hrefs) (parse-aexp #'f ρ u κ)]
		   [(e e-hrefs) (parse-aexp #'e ρ u κ)]
		   [(k k-hrefs) (parse-cont #'k ρ u κ)])
	(values #`(uapp #,f #,e #,k)
		(append f-hrefs e-hrefs k-hrefs)))])))

(define-syntax (P stx)
  (syntax-case stx (λ)
    [(_ (λ (x k) e))
     (let-values ([(e hrefs) (parse-call #'e (list #'x) #'x #'k)])
	#`(ulam #,(if (in-ρ #'x hrefs) #'(hvar 'x) #'(svar 'x)) (kvar 'k) #,e))]))

(define unP
  (match-lambda
   [(ulam x k e)
    `(λ (,(unP x) ,(unP k)) ,(unP e))]
   [(klam x e)
    `(λ (,(unP x)) ,(unP e))]
   [(uapp f e k)
    `(,(unP f) ,(unP e) ,(unP k))]
   [(kapp k e)
    `(,(unP k) ,(unP e))]
   [(or (svar x)
	(hvar x)
	(sref x)
	(href x))
    x]
   [(num n)
    n]))

(module+ main
  (ulam-e (kapp-e (ulam-e (P (λ (x k0) (k0 (λ (y k1) (x y k1)))))))))
