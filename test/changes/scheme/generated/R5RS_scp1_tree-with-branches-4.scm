; Changes:
; * removed: 0
; * added: 5
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 3
; * calls to id fun: 1
(letrec ((atom? (lambda (x)
                  (not (pair? x))))
         (maak-blad (lambda (type)
                      type))
         (geef-type (lambda (blad)
                      blad))
         (maak-knoop (lambda (deelbomen)
                       deelbomen))
         (geef-deelbomen (lambda (boom)
                           boom))
         (maak-hybride-tak (lambda (knopen)
                             knopen))
         (geef-knopen (lambda (tak)
                        (<change>
                           tak
                           ((lambda (x) x) tak))))
         (leeg? (lambda (boom)
                  (null? boom)))
         (knoop? (lambda (boom)
                   (pair? boom)))
         (blad? (lambda (boom)
                  (atom? boom)))
         (hybride-tak (maak-hybride-tak
                        (list
                           (maak-knoop
                              (list
                                 (maak-knoop (list (maak-blad 'appel) (maak-blad 'appel) (maak-blad 'blad)))
                                 (maak-blad 'peer)))
                           (maak-knoop (list (maak-blad 'blad) (maak-blad 'peer)))
                           (maak-knoop (list (maak-blad 'appel) (maak-knoop (list (maak-blad 'appel) (maak-blad 'blad))))))))
         (tak (maak-hybride-tak
                (list
                   (maak-knoop
                      (list
                         (maak-knoop (list (maak-blad 'appel) (maak-blad 'appel) (maak-blad 'blad)))
                         (maak-blad 'peer)))
                   (maak-knoop (list (maak-blad 'blad) (maak-blad 'peer) (maak-blad 'appel)))
                   (maak-knoop (list (maak-blad 'appel) (maak-knoop (list (maak-blad 'appel) (maak-blad 'blad))))))))
         (tel (lambda (boom)
                (<change>
                   ()
                   (blad? boom))
                (letrec ((combine-results (lambda (l1 l2)
                                            (list (+ (car l1) (car l2)) (+ (cadr l1) (cadr l2)) (+ (caddr l1) (caddr l2)))))
                         (tel-hulp (lambda (boom)
                                     (if (leeg? boom)
                                        (list 0 0 0)
                                        (if (if (blad? boom) (eq? boom 'appel) #f)
                                           (list 1 0 0)
                                           (if (if (blad? boom) (eq? boom 'peer) #f)
                                              (<change>
                                                 (list 0 1 0)
                                                 (if (blad? boom)
                                                    (list 0 0 1)
                                                    (tel-hulp-in (geef-knopen boom))))
                                              (<change>
                                                 (if (blad? boom)
                                                    (list 0 0 1)
                                                    (tel-hulp-in (geef-knopen boom)))
                                                 (list 0 1 0)))))))
                         (tel-hulp-in (lambda (lst)
                                        (<change>
                                           ()
                                           null?)
                                        (if (null? lst)
                                           (list 0 0 0)
                                           (combine-results (tel-hulp (car lst)) (tel-hulp-in (cdr lst)))))))
                   (tel-hulp boom))))
         (member? (lambda (x lst)
                    (pair? (memq x lst))))
         (normaal? (lambda (knoop)
                     (let ((types (map (lambda (x) (if (pair? x) 'tak x)) knoop)))
                        (not (if (member? 'appel types) (member? 'peer types) #f)))))
         (check-normaal (lambda (boom)
                          (if (leeg? boom)
                             (<change>
                                #t
                                (if (blad? boom)
                                   #t
                                   (if (knoop? boom)
                                      (if (normaal? boom)
                                         #f
                                         (check-normaal-in (geef-knopen boom)))
                                      (check-normaal-in (geef-knopen boom)))))
                             (<change>
                                (if (blad? boom)
                                   #t
                                   (if (knoop? boom)
                                      (if (normaal? boom)
                                         (check-normaal-in (geef-knopen boom))
                                         #f)
                                      (check-normaal-in (geef-knopen boom))))
                                #t))))
         (check-normaal-in (lambda (lst)
                             (<change>
                                ()
                                (car lst))
                             (<change>
                                ()
                                lst)
                             (if (null? lst)
                                #t
                                (if (check-normaal (car lst))
                                   (check-normaal-in (cdr lst))
                                   #f)))))
   (<change>
      ()
      __toplevel_cons)
   (if (equal? (tel hybride-tak) (__toplevel_cons 4 (__toplevel_cons 2 (__toplevel_cons 3 ()))))
      (check-normaal hybride-tak)
      #f))