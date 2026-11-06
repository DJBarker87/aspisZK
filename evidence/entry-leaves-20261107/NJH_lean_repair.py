from NJH_formal import *
for a,m in [('NJH_L008','NJH_SyscallLaws'),('NJH_L009','NJH_CopyWindow')]:
 r=run(a,'lean',m)
 if r['exit_status']:break
