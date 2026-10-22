; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Real)
(declare-fun s () Real)
(declare-fun L () Real)
(declare-fun t () Real)
(assert
 (> c 0.0))
(assert
 (> s 0.0))
(assert
 (= (+ (* c c) (* s s)) 1.0))
(assert
 (>= L 1.0))
(assert
 (<= (* c L) 1.0))
(assert
 (<= (* s L) 1.0))
(assert
 (= (* t s) (- 1.0 c)))
(assert
 (> t 0.0))
(assert
 (< t 1.0))
(assert
 (>= (- L 1.0) (* (/ 3.0 4.0) (- 1.0 t))))
(check-sat)
