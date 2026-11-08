from NMX_formal import *
for a,m in [(1230,'NMX_R6_AccountLeft'),(1231,'NMX_R7_Verify241'),(1232,'NMX_R7_Fold241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
