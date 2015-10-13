;--------------------------
;/home/baki/workspaces/default/ABC/test/jpf/WU_FTPD_10.smt2

(declare-fun cmd_1 () String)
(assert (not (contains (concat "/home/ftp/bin" (subString cmd_1  (lastIndexOf cmd_1 47 (indexOf cmd_1 32)))) "%n" )))
(assert ( <=  ( +  (len (subString cmd_1  (lastIndexOf cmd_1 47 (indexOf cmd_1 32)))) 13) 32))
(assert ( !=  (indexOf cmd_1 32) -1))
(check-sat)

