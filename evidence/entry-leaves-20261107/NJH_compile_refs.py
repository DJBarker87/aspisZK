from NJH_formal import *
for a,m in [('NJH_L004','NJH_Ref.Types'),('NJH_L005','NJH_Ref.Funs')]:
 r=run(a,'lean',m)
 if r['exit_status']:break
