#lang racket

(require data/bit-vector)
(require racket/generator)
(require math/number-theory)

(provide subsets-universal
         random-subset
         ord->set)

(module+ test
  (require rackunit))

(define (bit-vector-rightmost bv)
  (let ([len (bit-vector-length bv)])
    (define (scan offs lastfound)
      (cond [(>= offs len) lastfound]
            [(bit-vector-ref bv offs)
             (scan (add1 offs) offs)]
            [else
              (scan (add1 offs) lastfound)]))
    (scan 0 -1)))

(define (subsets-universal maxval size)
  (in-generator

    (define bt (make-bit-vector size #f))
    (define v (make-vector size 1))

    (let loop ([pos 0])
      (let* ([lastval (vector-ref v pos)]
             [limit (+ (- maxval size) pos 1)])
        (if (>= (add1 pos) size)
            (begin
              (for ([i (in-range lastval (add1 maxval))])
                (vector-set! v pos i)
                (yield (vector->list v)))
              (bit-vector-set! bt pos #f)
              (let ([rightmost (bit-vector-rightmost bt)])
                (when (>= rightmost 0)
                  (bit-vector-set! bt rightmost #f)
                  (vector-set! v rightmost (add1 (vector-ref v rightmost)))
                  (loop rightmost))))
            (let ([shouldbt (not (= lastval limit))])
              (bit-vector-set! bt pos shouldbt)
              (vector-set! v (add1 pos) (add1 lastval))
              (loop (add1 pos))))))))

(define/contract (ord->set ord n k)
  (->i ([ord (n k) (and/c exact-integer? (between/c 0 (sub1 (binomial n k))))]
        [n exact-integer?]
        [k (n) (and/c exact-integer? (<=/c n))])
       [result list?])
       
  (define (work base remainder k)
    (when (> base n)
      (error "base too big " n))
    (define (check i remainder)
      (when (> (+ base i) n)
        (error "check too big " (+ base i)))
      (if (= remainder 0)
          (values i remainder)
          (let* ([choices-to-right (- n base i)]
                 [t (binomial choices-to-right (sub1 k))])
            (if (>= remainder t)
                (check (add1 i) (- remainder t))
                (values i remainder)))))
    (cond
      [(= k 0) '()]
      [(= k 1) (list (+ base remainder))]
      [else
       (let-values ([(Δ remainder) (check 0 remainder)])
         (cons (+ base Δ) (work (+ base Δ 1) remainder (sub1 k))))]))
  
  (work 1 ord k))

(module+ test

  (define (check-ord n k)
    (for/and ([i (in-naturals)]
          [s (subsets-universal n k)])
      (let ([s-check (ord->set i n k)])
        (equal? s s-check))))

  (check-true (check-ord 11 5)))

; Random subset using only space k with runtime O(k) if k <= n/2, or O(klogk) otherwise
; Taken from https://www.math.upenn.edu/~wilf/website/CombinatorialAlgorithms.pdf
(define (random-subset n k)
  (define a (make-vector k 0))
  (for ([i (in-range 0 k)])
    (vector-set! a i (floor (/ (* i n) k))))
  (let loop ([c (sub1 k)])
    (let* ([x (random 1 (add1 n))]
           [l (floor (/ (- (* x k) 1) n))]
           [al (vector-ref a l)])
      (if (<= x al)
          (loop c)
          (begin
            (vector-set! a l (add1 al))
            (when (> c 0)
              (loop (sub1 c)))))))
  
  (define p 0)
  (for ([i (in-range 0 k)])
    (let* ([ai (vector-ref a i)]
           [lower-bound (floor (/ (* i n) k))])
      (vector-set! a i 0)
      (when (not (= ai lower-bound))
        (vector-set! a p ai)
        (set! p (add1 p)))))

  (set! p (sub1 p))
  
  (let loop ([p p] [s (sub1 k)])
    (let* ([ap (vector-ref a p)]
           [l (floor (/ (sub1 (* ap k)) n))]
           [start (floor (/ (* l n) k))]
           [Δs (- ap start)])
      (vector-set! a p 0)
      (vector-set! a s (add1 l))
      (when (> p 0)
        (loop (sub1 p) (- s Δs)))))

  (let outer ([l (sub1 k)])
    (let ([r l])
      (let* ([al (vector-ref a l)]
             [m0 (add1 (floor (/ (* (sub1 al) n) k)))]
             [m (add1 (- (floor (/ (* al n) k)) m0))])
        (when (< al 0) (error "Unexpected al"))

        (let inner ([l l]
                    [m m])
          (let ([i l]
                [x (+ m0 (random 0 m))])
            (let inner2 ()
              (set! i (add1 i))
              (when (<= i r)
                (let ([ai (vector-ref a i)])
                  (when (>= x ai)
                    (vector-set! a (sub1 i) ai)
                    (set! x (add1 x))
                    (inner2)))))
            (vector-set! a (sub1 i) x)
            (cond [(= l 0) a]
                  [(= (vector-ref a (sub1 l)) 0)
                   (inner (sub1 l) (sub1 m))]
                  [else
                   (outer (sub1 l))])))))))

(module+ test

  (define (check-subsets-percentages get total)
    (define counts (make-hash))
    (define max-count 20000)
  
    (for ([i (in-range 0 max-count)])
      (let ([S (get)])
        (hash-update! counts S add1 (λ () 0))))

    (define err 0.01)
    (for/and ([(s count) (in-hash counts)])
      (let* ([ideal (/ 1.0 total)]
             [percentage (/ (exact->inexact count) max-count)]
             [Δ (abs (- percentage ideal))])
        (< Δ err)))))

(module+ test
  (define (check-universal-percentages n k)
    (define (get)
      (random-subset n k))

    (check-subsets-percentages get (binomial n k)))
  (check-true (check-universal-percentages 7 4))) 

(define (subsets S size)
  (let* ([U (subsets-universal (vector-length S) size)]
         [U-vectors (sequence-map list->vector U)])
    ;(printf "~a\n" (sequence->list U))
    (define (map-set v)
      (vector-map (λ (i) (vector-ref S (- i 1))) v))
    (sequence-map map-set U-vectors)))

(module+ test

  (define (check-subsets C k)
    (let ([n (vector-length C)])
      (for/and ([ord (in-naturals)]
                [S (subsets C k)])
        (let* ([U (ord->set ord n k)]
               [mapped (map (λ (i) (vector-ref C (sub1 i))) U)])
          (equal? mapped (vector->list S))))))

  (define generic-subset-k 5)
  (define generic-subset-max 20)
  (let ([C (list->vector (sequence->list (in-range generic-subset-max -1 -1)))])
    (check-true (check-subsets C generic-subset-k))))

