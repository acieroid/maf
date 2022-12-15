#lang racket 

(require acontracts)
(parse-cmdline!)

;; Adapted from Savina benchmarks ("Dining Philosophers benchmarks", coming from Wikipedia)
(define Rounds 300)
(define NumForks 5)
(define NumPhilosophers NumForks)
(define counter
  (actor "counter" (n)
           (add (m) (become counter (+ n m)))
           (finish () (display n) (terminate))))
(define arbitrator
  (actor "abritrator" (forks num-exited)
           (hungry (p id)
                   (let ((left id) (right (modulo (+ id 1) NumForks)))
                     (if (or (vector-ref forks left) (vector-ref forks right))
                         (send p denied)
                         (begin
                           ;; Modeled as side effects, probably not the best thing to do...
                           ;; but since there is only one arbitrator, that should be fine
                           (vector-set! forks left #t)
                           (vector-set! forks right #t)
                           (send p eat))))
                   (become arbitrator forks num-exited))
           (done (id)
                 (let ((left id) (right (modulo (+ id 1) NumForks)))
                   (vector-set! forks left #f)
                   (vector-set! forks right #f))
                 (become arbitrator forks num-exited))
           (exit ()
                 (if (= (+ num-exited 1) NumForks)
                     (terminate)
                     (become arbitrator forks (+ num-exited 1))))))
(define philosopher
  (actor "philosopher" (id rounds-so-far local-counter)
           (denied ()
                   (send arbitrator-actor hungry self id)
                   (become philosopher id rounds-so-far (+ local-counter 1)))
           (eat ()
                (send counter-actor add local-counter)
                (send arbitrator-actor done id)
                (if (< (+ rounds-so-far 1) Rounds)
                    (begin
                      ;; was: (send self start)
                      (send arbitrator-actor hungry self id)
                      (become philosopher id (+ rounds-so-far 1) local-counter))
                    (begin
                      (send arbitrator-actor exit)
                      (terminate))))
           (start ()
                  (send arbitrator-actor hungry self id)
                  (become philosopher id rounds-so-far local-counter))))

(define counter/c (behavior/c (any/c any/c)
  (add (integer?) unconstrained/c)
  (finish () unconstrained/c)))

;; TODO: specify a contract that the philosopher should contact the arbitrator again 
(define philosopher/c (behavior/c (any/c any/c)
  (denied () unconstrained/c)
  (eat () unconstrained/c)
  (start () unconstrained/c)))

; TODO: for add specify an or/c contract on the behavior
(define arbitrator/c (behavior/c (any/c any/c)
 (hungry (philosopher/c integer?) unconstrained/c)
 (done (integer?) unconstrained/c)
 (exit () unconstrained/c)))


(define counter-actor (create/c counter/c counter 0))
(define arbitrator-actor (create/c arbitrator/c arbitrator (make-vector NumForks #f) 0))
(define (create-philosophers i)
  (if (= i NumPhilosophers)
      #t
      (let ((p (create/c philosopher/c philosopher i 0 0)))
        (send p start)
        (create-philosophers (+ i 1)))))
(create-philosophers 0)

(print-statistics)
