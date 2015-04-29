(set-logic QF_S)

(declare-fun T_1 () Bool)
(declare-fun T_2 () Bool)
(declare-fun T_3 () Bool)
(declare-fun T_4 () Bool)
(declare-fun T_5 () Bool)
(declare-fun var_0xINPUT_80591 () String)

(assert (= T_1 (not (= "6JX7G3VKFq" var_0xINPUT_80591))))
(assert T_1)
(assert (= T_2 (not (= "" var_0xINPUT_80591))))
(assert T_2)
(assert (= T_3 (= var_0xINPUT_80591 "Example:")))
(assert (= T_4 (not T_3)))
(assert T_4)
(assert (= T_5 (not (= var_0xINPUT_80591 "fB9De3KAY9"))))
(assert T_5)

(check-sat)

