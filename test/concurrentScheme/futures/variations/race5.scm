(letrec ((counter 0)
         (inc (lambda ()
                (set! counter (+ counter 1))))
         (dec (lambda ()
                (set! counter (- counter 1))))
         (t1 (future (inc)))
         (t2 (future (dec)))
         (t3 (future (inc)))
         (t4 (future (dec)))
         (t5 (future (inc))))
  (deref t1)
  (deref t2)
  (deref t3)
  (deref t4)
  (deref t5)
  counter)
