(set-logic QF_S)

(declare-fun var_abc () String)

(assert (not (str.in.re var_abc (re.++ (str.to.re "G") (str.to.re "o") (str.to.re "o") (str.to.re "g") (str.to.re "l") (str.to.re "e") (str.to.re "A") (str.to.re "d") (str.to.re "S") (str.to.re "e") (str.to.re "r") (str.to.re "v") (str.to.re "i") (str.to.re "n") (str.to.re "g") (str.to.re "T") (str.to.re "e") (str.to.re "s") (str.to.re "t") (str.to.re "="))))) 

(check-sat)

