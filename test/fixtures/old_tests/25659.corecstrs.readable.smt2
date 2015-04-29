(set-logic QF_S)

(declare-fun I0_2 () Int)
(declare-fun PCTEMP_LHS_1 () Int)
(declare-fun T0_2 () String)
(declare-fun T1_2 () String)
(declare-fun T2_2 () String)
(declare-fun T3_2 () String)
(declare-fun T4_2 () String)
(declare-fun T5_2 () String)
(declare-fun T_2 () Bool)
(declare-fun T_3 () Bool)
(declare-fun T_SELECT_1 () Bool)
(declare-fun var_0xINPUT_13159 () String)

(assert (= T_SELECT_1 (not (= PCTEMP_LHS_1 (- 1)))))
(assert (ite T_SELECT_1 
	(and (= PCTEMP_LHS_1 (+ I0_2 0))(= var_0xINPUT_13159 (str.++ T0_2 T1_2))(= I0_2 (str.len T4_2))(= 0 (str.len T0_2))(= T1_2 (str.++ T2_2 T3_2))(= T2_2 (str.++ T4_2 T5_2))(= T5_2 "__utmz=169413169.")(not (str.in.re T4_2 (re.++ (str.to.re "_") (str.to.re "_") (str.to.re "u") (str.to.re "t") (str.to.re "m") (str.to.re "z") (str.to.re "=") (str.to.re "1") (str.to.re "6") (str.to.re "9") (str.to.re "4") (str.to.re "1") (str.to.re "3") (str.to.re "1") (str.to.re "6") (str.to.re "9") (str.to.re "."))))) 
	(and (= PCTEMP_LHS_1 (- 1))(= var_0xINPUT_13159 (str.++ T0_2 T1_2))(= 0 (str.len T0_2))(not (str.in.re T1_2 (re.++ (str.to.re "_") (str.to.re "_") (str.to.re "u") (str.to.re "t") (str.to.re "m") (str.to.re "z") (str.to.re "=") (str.to.re "1") (str.to.re "6") (str.to.re "9") (str.to.re "4") (str.to.re "1") (str.to.re "3") (str.to.re "1") (str.to.re "6") (str.to.re "9") (str.to.re ".")))))))
(assert (= T_2 (< (- 1) PCTEMP_LHS_1)))
(assert T_2)
(assert (= T_3 (= "" var_0xINPUT_13159)))
(assert T_3)

(check-sat)

