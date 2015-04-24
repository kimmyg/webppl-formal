#lang racket/base
(require racket/match
         racket/set)

;; there should be different flavors of relations
;; for the different types of equality (eq, eqv, equal)

(struct rel2 (A B))
(struct rel3 (A B C))

(define (make-rel2) (rel2 (hash) (hash)))
(define (make-rel3) (rel3 (hash) (hash) (hash)))

(define ((add x) s)
  (set-add s x))

(define rel-add
  (case-lambda
    [(R a b)
     (match-let ([(rel2 A B) R]
                 [add (add (cons a b))])
       (rel2 (hash-update A a add (set))
             (hash-update B b add (set))))]
    [(R a b c)
     (match-let ([(rel3 A B C) R]
                 [add (add (list* a b c))])
       (rel3 (hash-update A a add (set))
             (hash-update B b add (set))
             (hash-update C c add (set))))]))

(define (rel-get R i v)
  (match R
    [(rel2 A B)
     (match i
       [0 (hash-ref A v (set))]
       [1 (hash-ref B v (set))])]
    [(rel3 A B C)
     (match i
       [0 (hash-ref A v (set))]
       [1 (hash-ref B v (set))]
       [2 (hash-ref C v (set))])]))

(define-match-expander ×
  (syntax-rules ()
    [(_ es ...)
     (list* es ...)]))

(provide (rename-out [make-rel2 rel2]
                     [make-rel3 rel3])
         rel-add
         rel-get
         ×)
