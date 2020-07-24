(define (phi x1 x2 x3 x4)
  (and (or x1 (not x2) (not x3) (<change> #t (not x4)))
       (or (<change> (not x2) x2) (not x3))
       (or (<change> #f (not x1)) x4 x2)))
(define (try f)
  (or (f #t) (f #f)))
(define (sat-solve-4 pred)
  (try (lambda (n1)
         (try (lambda (n2)
                (try (lambda (n3)
                       (try (lambda (n4)
                              (pred n1 n2 n3 n4))))))))))
(sat-solve-4 phi)