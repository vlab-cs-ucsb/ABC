(set-logic QF_S)

(declare-fun a () String)

(assert (begins a "" ))

(check-sat)

