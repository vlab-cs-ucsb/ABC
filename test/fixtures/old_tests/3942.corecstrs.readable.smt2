(set-logic QF_S)

(declare-fun PCTEMP_LHS_1 () String)
(declare-fun PCTEMP_LHS_1_idx_0 () String)
(declare-fun T0_2 () String)
(declare-fun T_2 () Int)
(declare-fun T_3 () Bool)
(declare-fun T_4 () Bool)
(declare-fun var_0xINPUT_174480 () String)

(assert (= T0_2 PCTEMP_LHS_1_idx_0))
(assert (= T0_2 var_0xINPUT_174480))
(assert (= T_2 (str.len PCTEMP_LHS_1)))
(assert (= T_3 (< 0 T_2)))
(assert (= T_4 (not T_3)))
(assert T_4)

(check-sat)

