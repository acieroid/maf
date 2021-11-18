; Changes:
; * removed: 0
; * added: 0
; * swaps: 0
; * negated predicates: 2
; * swapped branches: 1
; * calls to id fun: 1
(letrec ((make-point (lambda (x y)
                       (letrec ((dispatch (lambda (msg)
                                            (if (eq? msg 'x-value)
                                               x
                                               (if (eq? msg 'y-value) y (error "wrong message"))))))
                          dispatch)))
         (make-segment (lambda (start end)
                         (letrec ((midpoint (lambda ()
                                              (make-point (/ (+ (start 'x-value) (end 'x-value)) 2) (/ (+ (start 'y-value) (end 'y-value)) 2))))
                                  (dispatch (lambda (msg)
                                              (if (eq? msg 'start-point)
                                                 start
                                                 (if (eq? msg 'end-point)
                                                    end
                                                    (if (eq? msg 'midpoint)
                                                       (midpoint)
                                                       (error "wrong message")))))))
                            dispatch)))
         (make-w-vector (lambda args
                          (letrec ((dimension (lambda ()
                                                (length args)))
                                   (coordinate (lambda (n)
                                                 (<change>
                                                    (if (let ((__or_res (< n 1))) (if __or_res __or_res (> n (dimension))))
                                                       (error "coordinate is out of range")
                                                       (list-ref args (- n 1)))
                                                    ((lambda (x) x)
                                                       (if (let ((__or_res (< n 1))) (if __or_res __or_res (> n (dimension))))
                                                          (<change>
                                                             (error "coordinate is out of range")
                                                             (list-ref args (- n 1)))
                                                          (<change>
                                                             (list-ref args (- n 1))
                                                             (error "coordinate is out of range")))))))
                                   (add (lambda (w-vector)
                                          (letrec ((loop (lambda (ctr res)
                                                           (if (= ctr 0)
                                                              (apply make-w-vector res)
                                                              (loop (- ctr 1) (cons (+ (coordinate ctr) ((w-vector 'coordinate) ctr)) res))))))
                                             (loop (dimension) ()))))
                                   (dispatch (lambda (msg)
                                               (if (eq? msg 'dimension)
                                                  (dimension)
                                                  (if (eq? msg 'coordinate)
                                                     coordinate
                                                     (if (eq? msg 'add) add (error "wrong message")))))))
                             dispatch)))
         (make-polynome (lambda coefficients
                          (let ((polynome (apply make-w-vector coefficients)))
                             (letrec ((coefficient (lambda (index)
                                                     ((polynome 'coordinate) index)))
                                      (order (lambda ()
                                               (- (polynome 'dimension) 1)))
                                      (dispatch (lambda (msg)
                                                  (if (eq? msg 'order)
                                                     (order)
                                                     (if (eq? msg 'coefficient)
                                                        coefficient
                                                        (error "wrong message"))))))
                                dispatch))))
         (point1 (make-point 6 10))
         (point2 (make-point 10 20))
         (segment (make-segment point1 point2))
         (midpoint (segment 'midpoint))
         (w-vector1 (make-w-vector 1 2 3))
         (w-vector2 (make-w-vector 4 5 6))
         (polynome (make-polynome 1 2 3)))
   (if (= (point1 'x-value) 6)
      (if (<change> (= ((segment 'start-point) 'y-value) 10) (not (= ((segment 'start-point) 'y-value) 10)))
         (if (<change> (= (midpoint 'x-value) 8) (not (= (midpoint 'x-value) 8)))
            (if (= ((w-vector1 'coordinate) 2) 2)
               (if (= ((w-vector2 'coordinate) 1) 4)
                  (if (= ((((w-vector1 'add) w-vector2) 'coordinate) 1) 5)
                     (if (= (polynome 'order) 2)
                        (= ((polynome 'coefficient) 2) 2)
                        #f)
                     #f)
                  #f)
               #f)
            #f)
         #f)
      #f))