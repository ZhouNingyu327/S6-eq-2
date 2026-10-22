; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Real)
(declare-fun s () Real)
(declare-fun mu () Real)
(declare-fun d () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert
 (>= c 0.0))
(assert
 (>= s 0.0))
(assert
 (= (+ (* c c) (* s s)) 1.0))
(assert
 (> mu 1.0))
(assert
 (>= d 0.0))
(assert
 (>= x 0.0))
(assert
 (>= y 0.0))
(assert
 (>= (+ x y) 1.0))
(assert
 (let ((?x50 (+ (* c (- 0.0 d)) (* s (- 0.0 (- mu))))))
 (>= ?x50 (- 1.0))))
(assert
 (let ((?x50 (+ (* c (- 0.0 d)) (* s (- 0.0 (- mu))))))
 (<= ?x50 1.0)))
(assert
 (let ((?x54 (+ (* (- s) (- 0.0 d)) (* c (- 0.0 (- mu))))))
 (>= ?x54 (- 1.0))))
(assert
 (let ((?x54 (+ (* (- s) (- 0.0 d)) (* c (- 0.0 (- mu))))))
 (<= ?x54 1.0)))
(assert
 (let ((?x82 (+ (* c (- 0.0 (- x))) (* s 0.0))))
 (>= ?x82 (- 1.0))))
(assert
 (let ((?x82 (+ (* c (- 0.0 (- x))) (* s 0.0))))
 (<= ?x82 1.0)))
(assert
 (let ((?x84 (* c 0.0)))
 (let ((?x85 (+ (* (- s) (- 0.0 (- x))) ?x84)))
 (>= ?x85 (- 1.0)))))
(assert
 (let ((?x84 (* c 0.0)))
 (let ((?x85 (+ (* (- s) (- 0.0 (- x))) ?x84)))
 (<= ?x85 1.0))))
(assert
 (let ((?x100 (- 0.0 y)))
 (let ((?x101 (* s ?x100)))
 (let ((?x84 (* c 0.0)))
 (let ((?x102 (+ ?x84 ?x101)))
 (>= ?x102 (- 1.0)))))))
(assert
 (let ((?x100 (- 0.0 y)))
 (let ((?x101 (* s ?x100)))
 (let ((?x84 (* c 0.0)))
 (let ((?x102 (+ ?x84 ?x101)))
 (<= ?x102 1.0))))))
(assert
 (let ((?x100 (- 0.0 y)))
 (let ((?x104 (* c ?x100)))
 (let ((?x105 (+ (* (- s) 0.0) ?x104)))
 (>= ?x105 (- 1.0))))))
(assert
 (let ((?x100 (- 0.0 y)))
 (let ((?x104 (* c ?x100)))
 (let ((?x105 (+ (* (- s) 0.0) ?x104)))
 (<= ?x105 1.0)))))
(assert
 (let ((?x124 (+ (* c (- d (- x))) (* s (- (- mu) 0.0)))))
 (>= ?x124 (- 1.0))))
(assert
 (let ((?x124 (+ (* c (- d (- x))) (* s (- (- mu) 0.0)))))
 (<= ?x124 1.0)))
(assert
 (let ((?x127 (+ (* (- s) (- d (- x))) (* c (- (- mu) 0.0)))))
 (>= ?x127 (- 1.0))))
(assert
 (let ((?x127 (+ (* (- s) (- d (- x))) (* c (- (- mu) 0.0)))))
 (<= ?x127 1.0)))
(assert
 (let ((?x149 (+ (* c (- d 0.0)) (* s (- (- mu) y)))))
 (>= ?x149 (- 1.0))))
(assert
 (let ((?x149 (+ (* c (- d 0.0)) (* s (- (- mu) y)))))
 (<= ?x149 1.0)))
(assert
 (let ((?x152 (+ (* (- s) (- d 0.0)) (* c (- (- mu) y)))))
 (>= ?x152 (- 1.0))))
(assert
 (let ((?x152 (+ (* (- s) (- d 0.0)) (* c (- (- mu) y)))))
 (<= ?x152 1.0)))
(assert
 (let ((?x100 (- 0.0 y)))
 (let ((?x101 (* s ?x100)))
 (let ((?x175 (+ (* c (- (- x) 0.0)) ?x101)))
 (>= ?x175 (- 1.0))))))
(assert
 (let ((?x100 (- 0.0 y)))
 (let ((?x101 (* s ?x100)))
 (let ((?x175 (+ (* c (- (- x) 0.0)) ?x101)))
 (<= ?x175 1.0)))))
(assert
 (let ((?x100 (- 0.0 y)))
 (let ((?x104 (* c ?x100)))
 (let ((?x177 (+ (* (- s) (- (- x) 0.0)) ?x104)))
 (>= ?x177 (- 1.0))))))
(assert
 (let ((?x100 (- 0.0 y)))
(let ((?x104 (* c ?x100)))
(let ((?x177 (+ (* (- s) (- (- x) 0.0)) ?x104)))
(<= ?x177 1.0)))))
(check-sat)
