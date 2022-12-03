#lang racket
(require data/heap)
(provide sim? wire?
         (contract-out
          [make-sim        (-> sim?)]
          [sim-wait!       (-> sim? positive? void?)]
          [sim-time        (-> sim? real?)]
          [sim-add-action! (-> sim? positive? (-> any/c) void?)]

          [make-wire       (-> sim? wire?)]
          [wire-on-change! (-> wire? (-> any/c) void?)]
          [wire-value      (-> wire? boolean?)]
          [wire-set!       (-> wire? boolean? void?)]

          [bus-value (-> (listof wire?) natural?)]
          [bus-set!  (-> (listof wire?) natural? void?)]

          [gate-not  (-> wire? wire? void?)]
          [gate-and  (-> wire? wire? wire? void?)]
          [gate-nand (-> wire? wire? wire? void?)]
          [gate-or   (-> wire? wire? wire? void?)]
          [gate-nor  (-> wire? wire? wire? void?)]
          [gate-xor  (-> wire? wire? wire? void?)]

          [wire-not  (-> wire? wire?)]
          [wire-and  (-> wire? wire? wire?)]
          [wire-nand (-> wire? wire? wire?)]
          [wire-or   (-> wire? wire? wire?)]
          [wire-nor  (-> wire? wire? wire?)]
          [wire-xor  (-> wire? wire? wire?)]

          [flip-flop (-> wire? wire? wire? void?)]))

#| end of contracts, now the real code begins |#

#| action definitions |#

(struct action ;actions on the heap are supposed to be immutable for obvious reasons
  (time what)) 

#| end of action definitions |#

#| simulation definitions |#

(struct sim
  ([time #:mutable] [queue #:mutable]))

(define (make-sim)
  (sim 0 (make-heap (lambda (a b) (< (action-time a) (action-time b)))))) ;of course the queue should be ordered by actions' time of execution

(define (sim-wait! sim time)
  (let ([end-time (+ time (sim-time sim))])
    (if (= 0 (heap-count  (sim-queue sim)))
        (set-sim-time! sim end-time) ;nothing happens if the queue is empty
        (let ([A (heap-min (sim-queue sim))])
          (if (> (action-time A) end-time)
              (set-sim-time! sim end-time) ;nothing happens, the next action won't happen during the selected period of time
              (begin
                (heap-remove-min! (sim-queue sim))
                (set-sim-time! sim (action-time A))
                ((action-what A))
                (sim-wait! sim (- end-time (action-time A))))))))) ;we handle the next action on the queue 

(define (sim-add-action! sim delay what)
  (heap-add! (sim-queue sim) (action (+ (sim-time sim) delay) what)))

#| end of simulation definitions |#

#| wire definitions |#

(struct wire
  (sim [value #:mutable] [actions #:mutable]))

(define (make-wire sim)
  (wire sim #f '()))

(define (execute-actions l) ;executes all actions connected to the cable
  (if (null? l)
      (void)
      (begin
        ((car l))
        (execute-actions (cdr l)))))

(define (wire-set! wire value)
  (if (eq? value (wire-value wire))
      (void)
      (begin
        (set-wire-value! wire value)
        (execute-actions (wire-actions wire)))))

(define (wire-on-change! wire f)
  (set-wire-actions! wire (cons f (wire-actions wire)))
  (f)) ;actions must be executed when added

(define (wire-not wire1) ;constructs a not gate as well
  (let ([w_out (make-wire (wire-sim wire1))])
    (gate-not
     w_out
     wire1)
    w_out))

(define (wire-builder op wire1 wire2) ;constructor for wires (also calls the constructor of their corresponding gate)
  (if (eq? (wire-sim wire1) (wire-sim wire2))
        (let ([w_out (make-wire (wire-sim wire1))])
          (2gate-builder w_out wire1 wire2 op)
          w_out)
      (error "Wires from different simulations cannot be connected.")))

(define (wire-and wire1 wire2) (wire-builder (lambda (a b) (and a b)) wire1 wire2))

(define (wire-nand wire1 wire2) (wire-builder (lambda (a b) (nand a b)) wire1 wire2))

(define (wire-or wire1 wire2) (wire-builder (lambda (a b) (or a b)) wire1 wire2))

(define (wire-nor wire1 wire2) (wire-builder (lambda (a b) (nor a b)) wire1 wire2))

(define (wire-xor wire1 wire2) (wire-builder xor wire1 wire2))

#| end of wire definitions |#

#| bus definitions |#

(define (bus-set! wires value)
  (match wires
    ['() (void)]
    [(cons w wires)
     (begin
       (wire-set! w (= (modulo value 2) 1))
       (bus-set! wires (quotient value 2)))]))

(define (bus-value ws)
  (foldr (lambda (w value) (+ (if (wire-value w) 1 0) (* 2 value)))
         0
         ws))

#| end of bus definitions |#

#| gate definitions |#

(define (gate-not w_out w_in) ;not is the only gate with a single input
  (define (not-action) (wire-set! w_out (not (wire-value w_in))))
  (define (not-sim)
    (sim-add-action!
     (wire-sim w_out)
     1
     not-action))
  (if (eq? (wire-sim w_out) (wire-sim w_in))
      (begin
        (wire-on-change! w_in not-sim))
      (error "Wires from different simulations cannot be connected.")))

(define (2gate-builder w_out w_in1 w_in2 op) ;constructor for gates with two inputs
  (define (op-action) (wire-set! w_out (op (wire-value w_in1) (wire-value w_in2))))
  (define (op-sim)
    (sim-add-action!
     (wire-sim w_out)
     (if (eq? op xor) 2 1) ;xor is the only gate with delay=2
     op-action))
  (if (and (eq? (wire-sim w_out) (wire-sim w_in1)) (eq? (wire-sim w_out) (wire-sim w_in2)))
      (begin
        (wire-on-change! w_in1 op-sim)
        (wire-on-change! w_in2 op-sim))
      (error "Wires from different simulations cannot be connected.")))
  

(define (gate-and w_out w_in1 w_in2) (2gate-builder w_out w_in1 w_in2 (lambda (a b) (and a b))))

(define (gate-nand w_out w_in1 w_in2) (2gate-builder w_out w_in1 w_in2 (lambda (a b) (nand a b))))

(define (gate-or w_out w_in1 w_in2) (2gate-builder w_out w_in1 w_in2 (lambda (a b) (or a b))))

(define (gate-nor w_out w_in1 w_in2) (2gate-builder w_out w_in1 w_in2 (lambda (a b) (nor a b))))

(define (gate-xor w_out w_in1 w_in2) (2gate-builder w_out w_in1 w_in2 xor)) 
         
#| end of gate definitions |#

(define (flip-flop out clk data)
  (define sim (wire-sim data))
  (define w1  (make-wire sim))
  (define w2  (make-wire sim))
  (define w3  (wire-nand (wire-and w1 clk) w2))
  (gate-nand w1 clk (wire-nand w2 w1))
  (gate-nand w2 w3 data)
  (gate-nand out w1 (wire-nand out w3)))
