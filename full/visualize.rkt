#lang racket
(require racket/system
	 racket/list
	 racket/string
         "analyze.rkt"
         "parse.rkt")

(define p0 (CPS (P ((λ (x) ((λ (y) (add1 y)) x)) ((λ () ((λ () 35))))))))

(define recursion
  (CPS (P ((λ (Y)
	     ((λ (geom)	(geom))
	      (Y (λ (geom) (λ () (if0 (flip) 0 (add1 (geom))))))))
	   (λ (f) ((λ (g0) (g0 g0))
		   (λ (f0) (λ () ((f (f0 f0)))))))))))

(define p1 (CPS (P ((λ (Y)
		     ((λ (f) ((λ (geom*) (geom*))
			      (Y (λ (geom*) (λ () (if0 (f) 0 (add1 (geom*))))))))
		      (λ () (if0 (flip) (flip) (flip)))))
		   (λ (f0) ((λ (g0) (g0 g0))
			    (λ (f1) (λ () ((f0 (f1 f1)))))))))))

(define (viz init seen calls tails summaries finals)
  (define (id ς)
    (number->string (abs (equal-hash-code ς)) 16))
  (define (• ς)
    (format "  ς~a [label=\"~a\"]"
	    (id ς)
	    (match ς
	      [(ς-entr σ f vs)
	       (if (symbol? f) f (unP (unCPS f)))]
	      [(ς-exit σ v)
	       (string-join (map (λ (v) (format "~a" v)) (set->list v)) ", ")]
	      [(ς-call σ ρ f es k ℓ)
	       `(,(unP (unCPS f)) ,@(map (λ (e) (unP (unCPS e))) es) ,ℓ)]
	      [(ς-tail σ ρ f es ℓ)
	       `(,(unP (unCPS f)) ,@(map (λ (e) (unP (unCPS e))) es) ,ℓ)]))

)
  (define (-> ς0 ς1 . attrs)
    (format "ς~a -> ς~a [~a]" (id ς0) (id ς1) (string-join attrs " ")))
  (flatten (list "digraph cfg {"
		 (for/list ([ς0×ς1 (in-set seen)])
		   (• (cdr ς0×ς1)))
		 (for/list ([(ς2 ς0×ς1s) (in-hash calls)])
		   (for/list ([ς0×ς1 (in-set ς0×ς1s)])
		     (list (-> (car ς0×ς1) (cdr ς0×ς1))
			   (-> (cdr ς0×ς1) ς2 "style=dotted"))))
		 (for/list ([(ς2 ς0×ς1s) (in-hash tails)])
		   (for/list ([ς0×ς1 (in-set ς0×ς1s)])
		     (list (-> (car ς0×ς1) (cdr ς0×ς1))
			   (-> (cdr ς0×ς1) ς2 "style=dotted"))))
		 #;
		 (for/list ([ς0×ς1 (in-set seen)])
		 (-> (car ς0×ς1) (cdr ς0×ς1)))
		 (for/list ([(ς0 ς1s) (in-hash summaries)])
		   (for/list ([ς1 (in-set ς1s)])
		     (-> ς0 ς1 "style=dashed")))
		 "}")))


(let-values ([(init seen calls tails summaries finals) (time (analyze p1))])
  (with-output-to-file "cfg.gv"
    (λ () (for-each displayln (viz init seen calls tails summaries finals)))
    #:exists 'replace)
  (system "dot -Tpdf -o cfg.pdf cfg.gv && zathura cfg.pdf"))
