from NMX_formal import *
for a,m in [(1223,'NMX_R6_Validation'),(1224,'NMX_R6_AccountLeft')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
