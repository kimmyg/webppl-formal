#lang racket

(define (return v)
  (hash v 1))

(define (>>= m f)
  (for/fold ([m (hash)])
      ([(v p) (in-hash m)])
    (for/fold ([m m])
        ([(v p0) (in-hash (f v))])
      (hash-update m v (λ (p1) (+ p1 (* p0 p))) 0))))

(>>= (return 'stop) (λ (x) (hash x 1/2 #f 1/2)))

(struct D ())
(struct S D (v))
(struct B D (p D0 D1))

(define f (B 1/2 (S add1) (S sub1)))
(define x (B 1/2 (S 1) (S 2)))

#;
(define (apply f x)
  (match f
    [(S f) (apply0 f x)]
    [()]))

#;(apply f x)

(>>= (hash add1 1/2 values 1/2) (λ (f) (>>= (hash 1 1/2 2 1/2) (λ (x) (return (f x))))))
