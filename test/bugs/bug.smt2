(declare-fun NEW_P () String)

(assert (not (contains (toLower NEW_P) "abc-16")))
(assert (not (contains "abc-16" (toLower NEW_P))))
(assert (not (contains (toLower NEW_P) "61-cba")))
(assert (not (contains "61-cba" (toLower NEW_P))))

(check-sat)