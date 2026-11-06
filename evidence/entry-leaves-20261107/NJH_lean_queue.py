from NJH_formal import *
for a,m in [('NJH_L006','NJH_SyscallLaws'),('NJH_L007','NJH_CopyWindow')]:
 r=run(a,'lean',m)
 if r['exit_status']:break
