; Changes:
; * removed: 0
; * added: 1
; * swaps: 2
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 1
(letrec ((result ())
         (output (lambda (i)
                   (set! result (cons i result))))
         (hulp 2)
         (haha (lambda (x)
                 (<change>
                    (let ((hulp (* x hulp)))
                       (output hulp))
                    ((lambda (x) x) (let ((hulp (* x hulp))) (output hulp))))
                 (<change>
                    (output hulp)
                    (set! hulp 4))
                 (<change>
                    (set! hulp 4)
                    (output hulp)))))
   (<change>
      (haha 2)
      (haha 3))
   (<change>
      (haha 3)
      (haha 2))
   (<change>
      ()
      __toplevel_cons)
   (equal? result (__toplevel_cons 4 (__toplevel_cons 12 (__toplevel_cons 2 (__toplevel_cons 4 ()))))))