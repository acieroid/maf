; Changes:
; * removed: 0
; * added: 1
; * swaps: 0
; * negated predicates: 2
; * swapped branches: 1
; * calls to id fun: 1
(letrec ((comprimeer (lambda (metingen)
                       (letrec ((hulp (lambda (lst prev count)
                                        (<change>
                                           (if (null? lst)
                                              (list (list prev count))
                                              (if (= (car lst) prev)
                                                 (hulp (cdr lst) prev (+ count 1))
                                                 (cons (list prev count) (hulp (cdr lst) (car lst) 1))))
                                           ((lambda (x) x)
                                              (if (null? lst)
                                                 (list (list prev count))
                                                 (if (<change> (= (car lst) prev) (not (= (car lst) prev)))
                                                    (hulp (cdr lst) prev (+ count 1))
                                                    (cons (list prev count) (hulp (cdr lst) (car lst) 1)))))))))
                          (if (null? metingen)
                             ()
                             (hulp (cdr metingen) (car metingen) 1)))))
         (comprimeer-iter (lambda (metingen)
                            (<change>
                               ()
                               prev)
                            (letrec ((hulp (lambda (lst prev count res)
                                             (if (null? lst)
                                                (reverse (cons (list prev count) res))
                                                (if (= (car lst) prev)
                                                   (hulp (cdr lst) prev (+ count 1) res)
                                                   (hulp (cdr lst) (car lst) 1 (cons (list prev count) res)))))))
                               (if (<change> (null? metingen) (not (null? metingen)))
                                  ()
                                  (hulp (cdr metingen) (car metingen) 1 ()))))))
   (if (equal? (comprimeer (__toplevel_cons 3.750000e+01 (__toplevel_cons 3.750000e+01 (__toplevel_cons 3.720000e+01 (__toplevel_cons 3.800000e+01 (__toplevel_cons 3.800000e+01 (__toplevel_cons 3.800000e+01 (__toplevel_cons 3.830000e+01 ())))))))) (__toplevel_cons (__toplevel_cons 3.750000e+01 (__toplevel_cons 2 ())) (__toplevel_cons (__toplevel_cons 3.720000e+01 (__toplevel_cons 1 ())) (__toplevel_cons (__toplevel_cons 3.800000e+01 (__toplevel_cons 3 ())) (__toplevel_cons (__toplevel_cons 3.830000e+01 (__toplevel_cons 1 ())) ())))))
      (<change>
         (equal?
            (comprimeer-iter
               (__toplevel_cons
                  3.750000e+01
                  (__toplevel_cons
                     3.750000e+01
                     (__toplevel_cons
                        3.720000e+01
                        (__toplevel_cons
                           3.800000e+01
                           (__toplevel_cons 3.800000e+01 (__toplevel_cons 3.800000e+01 (__toplevel_cons 3.830000e+01 ()))))))))
            (__toplevel_cons
               (__toplevel_cons 3.750000e+01 (__toplevel_cons 2 ()))
               (__toplevel_cons
                  (__toplevel_cons 3.720000e+01 (__toplevel_cons 1 ()))
                  (__toplevel_cons
                     (__toplevel_cons 3.800000e+01 (__toplevel_cons 3 ()))
                     (__toplevel_cons (__toplevel_cons 3.830000e+01 (__toplevel_cons 1 ())) ())))))
         #f)
      (<change>
         #f
         (equal?
            (comprimeer-iter
               (__toplevel_cons
                  3.750000e+01
                  (__toplevel_cons
                     3.750000e+01
                     (__toplevel_cons
                        3.720000e+01
                        (__toplevel_cons
                           3.800000e+01
                           (__toplevel_cons 3.800000e+01 (__toplevel_cons 3.800000e+01 (__toplevel_cons 3.830000e+01 ()))))))))
            (__toplevel_cons
               (__toplevel_cons 3.750000e+01 (__toplevel_cons 2 ()))
               (__toplevel_cons
                  (__toplevel_cons 3.720000e+01 (__toplevel_cons 1 ()))
                  (__toplevel_cons
                     (__toplevel_cons 3.800000e+01 (__toplevel_cons 3 ()))
                     (__toplevel_cons (__toplevel_cons 3.830000e+01 (__toplevel_cons 1 ())) ()))))))))