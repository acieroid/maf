; Changes:
; * removed: 2
; * added: 0
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 1
(letrec ((result ())
         (output (lambda (i)
                   (set! result (cons i result))))
         (make-ring (lambda (n)
                      (let ((last (cons 0 ())))
                         (<change>
                            (letrec ((build-list (lambda (n)
                                                   (if (= n 0) last (cons n (build-list (- n 1)))))))
                               (let ((ring (build-list n)))
                                  (set-cdr! last ring)
                                  ring))
                            ((lambda (x) x)
                               (letrec ((build-list (lambda (n)
                                                      (if (= n 0) last (cons n (build-list (- n 1)))))))
                                  (let ((ring (build-list n)))
                                     (set-cdr! last ring)
                                     ring)))))))
         (print-ring (lambda (r)
                       (letrec ((aux (lambda (l)
                                       (if (not (null? l))
                                          (if (eq? (cdr l) r)
                                             (begin
                                                (output " ")
                                                (<change>
                                                   (output (car l))
                                                   ())
                                                (output "..."))
                                             (begin
                                                (<change>
                                                   (output " ")
                                                   ())
                                                (output (car l))
                                                (aux (cdr l))))
                                          #f))))
                          (aux r)
                          #t)))
         (r (make-ring 3)))
   (print-ring r)
   (print-ring (cdr r))
   (equal?
      result
      (__toplevel_cons
         "..."
         (__toplevel_cons
            3
            (__toplevel_cons
               " "
               (__toplevel_cons
                  0
                  (__toplevel_cons
                     " "
                     (__toplevel_cons
                        1
                        (__toplevel_cons
                           " "
                           (__toplevel_cons
                              2
                              (__toplevel_cons
                                 " "
                                 (__toplevel_cons
                                    "..."
                                    (__toplevel_cons
                                       0
                                       (__toplevel_cons
                                          " "
                                          (__toplevel_cons
                                             1
                                             (__toplevel_cons
                                                " "
                                                (__toplevel_cons 2 (__toplevel_cons " " (__toplevel_cons 3 (__toplevel_cons " " ()))))))))))))))))))))