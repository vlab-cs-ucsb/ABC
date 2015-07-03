(set-logic QF_S)

(declare-fun abc () Int)
(declare-fun var_def () Int)

(assert (= abc def))

(check-sat-and-count 25)

