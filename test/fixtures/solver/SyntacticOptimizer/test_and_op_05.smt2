(set-logic QF_S)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(declare-fun f () Bool)

(assert	(and a (or (and b c) (and d e)) f (or (and b a) (and (and f e) (and d c)))))

(check-sat)

