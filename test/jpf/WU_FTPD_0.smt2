;--------------------------
;/home/baki/workspaces/default/ABC/test/jpf/WU_FTPD_0.smt2

(declare-fun cmd_1 () String)

(assert ( !=  (indexOf cmd_1 32) -1))
(check-sat)

