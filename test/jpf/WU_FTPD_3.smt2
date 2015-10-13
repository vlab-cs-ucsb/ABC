;--------------------------
;/home/baki/workspaces/default/ABC/test/jpf/WU_FTPD_3.smt2

(declare-fun cmd_1 () String)

(assert ( >  ( +  (len (subString cmd_1  (lastIndexOfChar cmd_1 47))) 13) 32))
(assert ( =  (indexOf cmd_1 32) -1))
(check-sat)

