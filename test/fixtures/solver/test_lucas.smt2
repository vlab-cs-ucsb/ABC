(set-logic QF_S)
(declare-fun var_0xINPUT_2 () String)
(declare-fun T2_2 () String)
(declare-fun T2_6 () String)
(declare-fun T_2 () String)
(declare-fun T1_6 () String)
(declare-fun T1_2 () String)
(declare-fun PCTEMP_LHS_1 () String)

(assert (and 

(= T1_6 (concat var_0xINPUT_2 "wil"))

(= T_2 (concat T1_6 "ie")) 

(not (= T_2 "lucas=wilie"))


))

(check-sat var_0xINPUT_2)

