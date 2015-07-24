(set-logic QF_S)

(declare-fun var_abc () String)

(assert (in var_abc /(abc|def)/ ))

(check-sat)

