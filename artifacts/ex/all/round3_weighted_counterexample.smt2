; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Real)
(declare-fun q () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun r () Real)
(assert
 (>= p 0.0))
(assert
 (>= q 0.0))
(assert
 (= (+ (* p p) (* q q)) 1.0))
(assert
 (>= x 0.0))
(assert
 (>= y 0.0))
(assert
 (>= r 0.0))
(assert
 (> (+ (+ x y) (* (/ 3.0 4.0) r)) 2.0))
(assert
 (let ((?x50 (* q 0.0)))
 (let ((?x51 (+ (* p (- 0.0 (- x))) ?x50)))
 (>= ?x51 (- 1.0)))))
(assert
 (let ((?x50 (* q 0.0)))
 (let ((?x51 (+ (* p (- 0.0 (- x))) ?x50)))
 (<= ?x51 1.0))))
(assert
 (let ((?x54 (* p 0.0)))
 (let ((?x55 (+ (* (- q) (- 0.0 (- x))) ?x54)))
 (>= ?x55 (- 1.0)))))
(assert
 (let ((?x54 (* p 0.0)))
 (let ((?x55 (+ (* (- q) (- 0.0 (- x))) ?x54)))
 (<= ?x55 1.0))))
(assert
 (let ((?x50 (* q 0.0)))
 (let ((?x74 (+ (* p (- 0.0 r)) ?x50)))
 (>= ?x74 (- 1.0)))))
(assert
 (let ((?x50 (* q 0.0)))
 (let ((?x74 (+ (* p (- 0.0 r)) ?x50)))
 (<= ?x74 1.0))))
(assert
 (let ((?x54 (* p 0.0)))
 (let ((?x76 (+ (* (- q) (- 0.0 r)) ?x54)))
 (>= ?x76 (- 1.0)))))
(assert
 (let ((?x54 (* p 0.0)))
 (let ((?x76 (+ (* (- q) (- 0.0 r)) ?x54)))
 (<= ?x76 1.0))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x91 (* q ?x90)))
 (let ((?x54 (* p 0.0)))
 (let ((?x92 (+ ?x54 ?x91)))
 (>= ?x92 (- 1.0)))))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x91 (* q ?x90)))
 (let ((?x54 (* p 0.0)))
 (let ((?x92 (+ ?x54 ?x91)))
 (<= ?x92 1.0))))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x94 (* p ?x90)))
 (let ((?x95 (+ (* (- q) 0.0) ?x94)))
 (>= ?x95 (- 1.0))))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x94 (* p ?x90)))
 (let ((?x95 (+ (* (- q) 0.0) ?x94)))
 (<= ?x95 1.0)))))
(assert
 (let ((?x50 (* q 0.0)))
 (let ((?x112 (+ (* p (- (- x) r)) ?x50)))
 (>= ?x112 (- 1.0)))))
(assert
 (let ((?x50 (* q 0.0)))
 (let ((?x112 (+ (* p (- (- x) r)) ?x50)))
 (<= ?x112 1.0))))
(assert
 (let ((?x54 (* p 0.0)))
 (let ((?x114 (+ (* (- q) (- (- x) r)) ?x54)))
 (>= ?x114 (- 1.0)))))
(assert
 (let ((?x54 (* p 0.0)))
 (let ((?x114 (+ (* (- q) (- (- x) r)) ?x54)))
 (<= ?x114 1.0))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x91 (* q ?x90)))
 (let ((?x138 (+ (* p (- (- x) 0.0)) ?x91)))
 (>= ?x138 (- 1.0))))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x91 (* q ?x90)))
 (let ((?x138 (+ (* p (- (- x) 0.0)) ?x91)))
 (<= ?x138 1.0)))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x94 (* p ?x90)))
 (let ((?x140 (+ (* (- q) (- (- x) 0.0)) ?x94)))
 (>= ?x140 (- 1.0))))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x94 (* p ?x90)))
 (let ((?x140 (+ (* (- q) (- (- x) 0.0)) ?x94)))
 (<= ?x140 1.0)))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x91 (* q ?x90)))
 (let ((?x154 (+ (* p (- r 0.0)) ?x91)))
 (>= ?x154 (- 1.0))))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x91 (* q ?x90)))
 (let ((?x154 (+ (* p (- r 0.0)) ?x91)))
 (<= ?x154 1.0)))))
(assert
 (let ((?x90 (- 0.0 y)))
 (let ((?x94 (* p ?x90)))
 (let ((?x156 (+ (* (- q) (- r 0.0)) ?x94)))
 (>= ?x156 (- 1.0))))))
(assert
 (let ((?x90 (- 0.0 y)))
(let ((?x94 (* p ?x90)))
(let ((?x156 (+ (* (- q) (- r 0.0)) ?x94)))
(<= ?x156 1.0)))))
(check-sat)
