from NMX_formal import *
for a,m in [(1247,'NMX_R7_LiftMember'),(1248,'NMX_R7_Port241'),(1249,'NMX_R7_PortLaw241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
