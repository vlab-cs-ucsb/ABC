(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (lastIndexOf /ucsbvlababcd/ /(sb|bc)/)))

(check-sat)

