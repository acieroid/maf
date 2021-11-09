; Changes:
; * removed: 0
; * added: 2
; * swaps: 2
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 1
(letrec ((result ())
         (output (lambda (i)
                   (<change>
                      ()
                      cons)
                   (set! result (cons i result))))
         (make-ring (lambda (n)
                      (let ((last (cons 0 ())))
                         (letrec ((build-list (lambda (n)
                                                (if (= n 0) last (cons n (build-list (- n 1)))))))
                            (let ((ring (build-list n)))
                               (set-cdr! last ring)
                               ring)))))
         (print-ring (lambda (r)
                       (letrec ((aux (lambda (l)
                                       (if (not (null? l))
                                          (if (eq? (cdr l) r)
                                             (begin
                                                (output " ")
                                                (output (car l))
                                                (output "..."))
                                             (begin
                                                (output " ")
                                                (output (car l))
                                                (aux (cdr l))))
                                          #f))))
                          (aux r)
                          #t)))
         (copy-ring (lambda (r)
                      (<change>
                         (letrec ((last ())
                                  (aux (lambda (l)
                                         (if (eq? (cdr l) r)
                                            (begin
                                               (set! last (cons (car l) ()))
                                               last)
                                            (cons (car l) (aux (cdr l)))))))
                            (let ((first (aux r)))
                               (set-cdr! last first)
                               first))
                         ((lambda (x) x)
                            (letrec ((last ())
                                     (aux (lambda (l)
                                            (if (eq? (cdr l) r)
                                               (begin
                                                  (set! last (cons (car l) ()))
                                                  last)
                                               (cons (car l) (aux (cdr l)))))))
                               (let ((first (aux r)))
                                  (set-cdr! last first)
                                  first))))))
         (right-rotate (lambda (r)
                         (letrec ((iter (lambda (l)
                                          (if (eq? (cdr l) r) l (iter (cdr l))))))
                            (iter r))))
         (Josephus (lambda (r n)
                     (letrec ((remove-nth! (lambda (l n)
                                             (if (<= n 2)
                                                (begin
                                                   (<change>
                                                      (set-cdr! l (cddr l))
                                                      (cdr l))
                                                   (<change>
                                                      (cdr l)
                                                      (set-cdr! l (cddr l))))
                                                (remove-nth! (cdr l) (- n 1)))))
                              (iter (lambda (l)
                                      (print-ring l)
                                      (<change>
                                         ()
                                         eq?)
                                      (if (eq? l (cdr l))
                                         (car l)
                                         (iter (remove-nth! l n))))))
                        (if (= n 1)
                           (car (right-rotate r))
                           (iter (copy-ring r))))))
         (ring (make-ring 5)))
   (Josephus ring 5)
   (<change>
      (print-ring ring)
      (equal?
         result
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
                        (__toplevel_cons
                           2
                           (__toplevel_cons
                              " "
                              (__toplevel_cons
                                 3
                                 (__toplevel_cons
                                    " "
                                    (__toplevel_cons
                                       4
                                       (__toplevel_cons
                                          " "
                                          (__toplevel_cons
                                             5
                                             (__toplevel_cons
                                                " "
                                                (__toplevel_cons
                                                   "..."
                                                   (__toplevel_cons
                                                      5
                                                      (__toplevel_cons
                                                         " "
                                                         (__toplevel_cons
                                                            "..."
                                                            (__toplevel_cons
                                                               5
                                                               (__toplevel_cons
                                                                  " "
                                                                  (__toplevel_cons
                                                                     3
                                                                     (__toplevel_cons
                                                                        " "
                                                                        (__toplevel_cons
                                                                           "..."
                                                                           (__toplevel_cons
                                                                              3
                                                                              (__toplevel_cons
                                                                                 " "
                                                                                 (__toplevel_cons
                                                                                    4
                                                                                    (__toplevel_cons
                                                                                       " "
                                                                                       (__toplevel_cons
                                                                                          5
                                                                                          (__toplevel_cons
                                                                                             " "
                                                                                             (__toplevel_cons
                                                                                                "..."
                                                                                                (__toplevel_cons
                                                                                                   3
                                                                                                   (__toplevel_cons
                                                                                                      " "
                                                                                                      (__toplevel_cons
                                                                                                         4
                                                                                                         (__toplevel_cons
                                                                                                            " "
                                                                                                            (__toplevel_cons
                                                                                                               5
                                                                                                               (__toplevel_cons
                                                                                                                  " "
                                                                                                                  (__toplevel_cons
                                                                                                                     0
                                                                                                                     (__toplevel_cons
                                                                                                                        " "
                                                                                                                        (__toplevel_cons
                                                                                                                           "..."
                                                                                                                           (__toplevel_cons
                                                                                                                              2
                                                                                                                              (__toplevel_cons
                                                                                                                                 " "
                                                                                                                                 (__toplevel_cons
                                                                                                                                    3
                                                                                                                                    (__toplevel_cons
                                                                                                                                       " "
                                                                                                                                       (__toplevel_cons
                                                                                                                                          4
                                                                                                                                          (__toplevel_cons
                                                                                                                                             " "
                                                                                                                                             (__toplevel_cons
                                                                                                                                                5
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   " "
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      0
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
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           2
                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                              " "
                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                 3
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    " "
                                                                                                                                                                                    (__toplevel_cons 4 (__toplevel_cons " " (__toplevel_cons 5 (__toplevel_cons " " ())))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   (<change>
      (equal?
         result
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
                        (__toplevel_cons
                           2
                           (__toplevel_cons
                              " "
                              (__toplevel_cons
                                 3
                                 (__toplevel_cons
                                    " "
                                    (__toplevel_cons
                                       4
                                       (__toplevel_cons
                                          " "
                                          (__toplevel_cons
                                             5
                                             (__toplevel_cons
                                                " "
                                                (__toplevel_cons
                                                   "..."
                                                   (__toplevel_cons
                                                      5
                                                      (__toplevel_cons
                                                         " "
                                                         (__toplevel_cons
                                                            "..."
                                                            (__toplevel_cons
                                                               5
                                                               (__toplevel_cons
                                                                  " "
                                                                  (__toplevel_cons
                                                                     3
                                                                     (__toplevel_cons
                                                                        " "
                                                                        (__toplevel_cons
                                                                           "..."
                                                                           (__toplevel_cons
                                                                              3
                                                                              (__toplevel_cons
                                                                                 " "
                                                                                 (__toplevel_cons
                                                                                    4
                                                                                    (__toplevel_cons
                                                                                       " "
                                                                                       (__toplevel_cons
                                                                                          5
                                                                                          (__toplevel_cons
                                                                                             " "
                                                                                             (__toplevel_cons
                                                                                                "..."
                                                                                                (__toplevel_cons
                                                                                                   3
                                                                                                   (__toplevel_cons
                                                                                                      " "
                                                                                                      (__toplevel_cons
                                                                                                         4
                                                                                                         (__toplevel_cons
                                                                                                            " "
                                                                                                            (__toplevel_cons
                                                                                                               5
                                                                                                               (__toplevel_cons
                                                                                                                  " "
                                                                                                                  (__toplevel_cons
                                                                                                                     0
                                                                                                                     (__toplevel_cons
                                                                                                                        " "
                                                                                                                        (__toplevel_cons
                                                                                                                           "..."
                                                                                                                           (__toplevel_cons
                                                                                                                              2
                                                                                                                              (__toplevel_cons
                                                                                                                                 " "
                                                                                                                                 (__toplevel_cons
                                                                                                                                    3
                                                                                                                                    (__toplevel_cons
                                                                                                                                       " "
                                                                                                                                       (__toplevel_cons
                                                                                                                                          4
                                                                                                                                          (__toplevel_cons
                                                                                                                                             " "
                                                                                                                                             (__toplevel_cons
                                                                                                                                                5
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   " "
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      0
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
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           2
                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                              " "
                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                 3
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    " "
                                                                                                                                                                                    (__toplevel_cons 4 (__toplevel_cons " " (__toplevel_cons 5 (__toplevel_cons " " ()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (print-ring ring)))