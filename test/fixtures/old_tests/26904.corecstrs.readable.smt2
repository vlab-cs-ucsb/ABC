(set-logic QF_S)

(declare-fun PCTEMP_LHS_1 () String)
(declare-fun PCTEMP_LHS_2 () String)
(declare-fun T1_3 () String)
(declare-fun T2_3 () String)
(declare-fun T_1 () String)
(declare-fun var_0xINPUT_24276 () String)

(assert (= T_1 (str.++ T1_3 T2_3)))
(assert (= T2_3 var_0xINPUT_24276))
(assert (= T1_3 "/signin"))
(assert (= PCTEMP_LHS_2 PCTEMP_LHS_1))
(assert (not (str.in.re PCTEMP_LHS_2 (str.to.re "%"))))

(check-sat)

