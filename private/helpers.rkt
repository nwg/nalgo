#lang racket/base

(require racket/sequence)
(require racket/set)

(provide set-immutable-copy
         sequence-max
         sequence-random-element
         set-random-element)

(define (set-immutable-copy s)
  (cond [(set-equal? s) (for/set ([i s]) i)]
        [(set-eqv? s) (for/seteqv ([i s]) i)]
        [(set-eq? s) (for/seteq ([i s]) i)]
        [else (error "Unknown set type")]))

(define (sequence-max seq)
  (sequence-fold (λ (v m) (if (> v m) v m)) -inf.0 seq))

(define (sequence-random-element seq)
  (sequence-ref seq (random 0 (sequence-length seq))))
  
(define (set-random-element s)
  (sequence-ref s (random 0 (set-count s))))

