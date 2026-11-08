from NMX_formal import *
for a,m in [(1339,'NMX_R8_Digest241'),(1340,'NMX_R8_GroupValidate241'),(1341,'NMX_R8_GroupHead241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
