(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (concat  /.{0,1}/ /(..)*/)))

(check-sat)

