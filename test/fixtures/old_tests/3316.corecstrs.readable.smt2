(set-logic QF_S)

(declare-fun T_1 () Bool)
(declare-fun T_2 () Bool)
(declare-fun T_3 () Bool)
(declare-fun T_5 () Bool)
(declare-fun T_7 () Bool)
(declare-fun T_9 () Bool)
(declare-fun T_b () Bool)
(declare-fun T_d () Bool)
(declare-fun var_0xINPUT_468893 () String)

(assert (= T_1 (= var_0xINPUT_468893 "Search")))
(assert (= T_2 (not T_1)))
(assert T_2)
(assert (= T_3 (= var_0xINPUT_468893 "Search")))
(assert (= T_5 (= var_0xINPUT_468893 "Search")))
(assert (= T_7 (= var_0xINPUT_468893 "Search")))
(assert (= T_9 (= var_0xINPUT_468893 "Search")))
(assert (= T_b (= var_0xINPUT_468893 "Search")))
(assert (= T_d (= var_0xINPUT_468893 "Search")))

(check-sat)

