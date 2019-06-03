(declare-fun str () String)

(assert (in str /(a|b)c*/))

(check-sat)
