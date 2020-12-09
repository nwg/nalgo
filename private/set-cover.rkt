#lang racket/base

(require racket/sequence)
(require racket/set)
(require data/bit-vector)
(require racket/generator)
(require racket/vector)
(require racket/bool)
(require math/number-theory)
(require "helpers.rkt")
(require "algorithms.rkt")

(provide uniform-scp)

(define (coefficient-matrix p num-rows rows num-cols cols)
  (define (coverage-bit-vector col)
    (for/bit-vector #:length num-rows
      ([row (rows)])
      ;(printf "checking p ~a ~a\n" row col)
      (p row col)))
  
  (for/vector #:length num-cols
    ([col (cols)])
    ;(printf "Built ~a for col ~a\n" (bit-vector->list (coverage-bit-vector col)) col)
    (coverage-bit-vector col)))
  
(define (bit-vector->ords bv)
  (in-generator
    (for ([bit (in-bit-vector bv)]
          [i (in-naturals)]
          #:when bit)
      (yield i))))

(define (uniform-scp p num-rows rows num-cols cols)
  (printf "Computing coefficients\n")
  (let ([M (coefficient-matrix p num-rows rows num-cols cols)])
    (printf "Done computing coefficients\n")


    (define (a i j)
      (let ([bv (vector-ref M j)])
        (bit-vector-ref bv i)))
    
    (define (S i)
      (for/bit-vector #:length num-cols
        ([j (in-range 0 num-cols)])
        (a i j)))
    
    (define (D j)
      (vector-ref M j))

    ;(printf "(D 0)=~a\n" (bit-vector->list (D 0)))
    ;(printf "(D 1)=~a\n" (bit-vector->list (D 1)))

    (define (all-rows-set)
      (for/seteqv ([i (in-range 0 num-rows)]) i))

    (define (all-cols-set)
      (for/seteqv ([j (in-range 0 num-cols)]) j))
    
    (define (constructive rows cols)
      (let ([I (set-copy rows)]
            [X (mutable-seteqv)]
            [d (make-vector num-cols 0)]
            [J (set-copy cols)])
        
        (let ([rows (set-immutable-copy rows)])
          (for ([j J])
            (let ([Dj (for/seteqv ([o (bit-vector->ords (D j))]) o)])
              (vector-set! d j (set-count (set-intersect rows Dj))))))

        (define (select-ticket)
          (printf "Selecting ticket\n")
          (let* ([uncovered (sequence-map (λ (j) (vector-ref d j)) J)]
                 [f (sequence-max uncovered)]
                 [J-candidates (sequence-filter (λ (j) (= (vector-ref d j) f)) J)]
                 [w (sequence-random-element J-candidates)])
            w))
        
        (define (process-ticket w)
          (printf "Processing ticket ~a\n" w)
          (set-add! X w)
          (set-remove! J w)

          (for ([i (bit-vector->ords (D w))]
                #:when (set-member? I i))
            (for ([j (bit-vector->ords (S i))])
              (vector-set! d j (sub1 (vector-ref d j))))
            (set-remove! I i))

          (printf "Finished processing ticket ~a\n" w))

        (let ([w (select-ticket)])
          (process-ticket w)

          (let loop ()
            (if (set-empty? I)
              (let* ([R (redundant X)])
                (set-subtract! X R)
                (set-immutable-copy X))
              (let* ([w (select-ticket)])
                (process-ticket w)
                (loop)))))))

    (define (redundant X)
      (let ([result (mutable-seteqv)]
            [v (make-vector num-rows 0)])
        (for ([j X])
          (for ([i (bit-vector->ords (D j))])
            (vector-set! v i (add1 (vector-ref v i)))))
        (for ([j X])
          (let* ([vs (for/list ([i (bit-vector->ords (D j))])
                       (vector-ref v i))]
                 [m (apply min vs)])
            (when (> m 1)
              (set-add! result j)
              (for ([i (bit-vector->ords (D j))])
                (vector-set! v i (sub1 (vector-ref v i)))))))
        result))

    (define (improvement rows cols X remove-col)
      (define (set-random-removal s amt)
        (when (> amt 0)
          (let ([e (set-random-element s)])
            (set-remove! s e))
          (set-random-removal s (sub1 amt))))
      
      (let ([Xp (set-copy X)]
            [D* (set-copy rows)]
            [S* (mutable-seteqv)])
        (set-random-removal Xp remove-col)
        (printf "Dropped tickets ~a\n" (set-subtract (set-immutable-copy X) Xp))
        (for* ([j Xp]
               [i (bit-vector->ords (D j))])
          (set-remove! D* i))
        (for* ([i D*]
               [j (bit-vector->ords (S i))])
          (set-add! S* j))

        (let ([X* (constructive D* S*)])
          (set-union! Xp X*)
          (let ([R (redundant Xp)])
            (set-subtract! Xp R))
          (if (<= (set-count Xp) (set-count X)) Xp X))))

    (define (verify X)
      (let ([coverage (make-bit-vector num-rows)])
        (for* ([j X]
               [i (bit-vector->ords (D j))])
          (bit-vector-set! coverage i #t))
        (= (bit-vector-popcount coverage) num-rows)))

    (define (removal-count c)
      (add1 (floor (/ c 2))))

    (define (run max-constructive max-improvement max-total)
      (printf "Beginning run: |S|=~a, |D|=~a\n" num-cols num-rows)
      (let* ([rows (all-rows-set)]
             [cols (all-cols-set)])

        (define (perform-run)
          (let ([X #f])
            
            (for ([i (in-range 1 (add1 max-constructive))])
              (printf "Running Constructive phase #~a/~a...\n" i max-constructive)
              (let ([X* (constructive rows cols)])
                (when (or (false? X) (< (set-count X*) (set-count X)))
                  (set! X X*)
                  (printf "Constructive: found set of length ~a\n" (set-count X)))))
            (when (not (verify X))
              (printf "Constructive solution ~a failed to cover all draws\n" (set->list X)))

            (printf "Beginning improvement stage with X length=~a\n" (set-count X))
            (for ([i (in-range 1 (add1 max-improvement))])
              (printf "Running Improvement phase #~a/~a... current X is ~a\n" i max-improvement (set->list X))
              (let* ([remove-count (removal-count (set-count X))]
                     [X* (improvement rows cols X remove-count)])
                (when (<= (set-count X*) (set-count X))
                  (set! X X*)
                  (printf "Improvement: improved set to length ~a -- ~a)\n" (set-count X) (set->list X)))))
            (printf "Finished Improvement Phase\n")
            (when (not (verify X))
              (printf "Improved solution ~a failed to cover all draws\n" (set->list X)))
            X))

        (let ([X #f])
          (for ([i (in-range 1 (add1 max-total))])
            (printf "Total: Beginning run ~a\n" i)
            (let ([X* (perform-run)])
              (if (false? X)
                  (set! X X*)
                  (when (< (set-count X*) (set-count X))
                    (set! X X*)
                    (printf "Total: found new set of length ~a\n" (set-count X)))))
            (printf "Total: End of run ~a\n" i))
          (set->list X))))

    (run 4 20 1)))

(module+ main
  (define n 16)
  (define k 4)
  (define p 4)
  (define t 2)
  (define (p-matches row col)
    (>= (set-count (set-intersect row col)) 2))
  
  (let* ([tickets (λ () (sequence-map list->seteqv (subsets-universal n k)))]
         [draws (λ () (sequence-map list->seteqv (subsets-universal n p)))]
         [solution (uniform-scp p-matches (binomial n p) draws (binomial n k) tickets)])
    (printf "Uniform set coverage, length=~a tickets=~a\n" (length solution) (map (λ (ord) (ord->set ord n k)) solution))))
  



