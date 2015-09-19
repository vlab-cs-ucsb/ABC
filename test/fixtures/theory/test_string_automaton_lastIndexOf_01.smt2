(set-logic QF_S)

(declare-fun var_abc () String)

;(assert (= var_abc (lastIndexOf /(abcbc|deb)/ "b")))
;(assert (= var_abc (lastIndexOf /(bbbb)+/ "b")))
;(assert (= var_abc (lastIndexOf /(abc|abcabc)/ "b")))
(assert (= var_abc (lastIndexOf /(abc|abcabc|abcdec)/ "b")))
(check-sat)

