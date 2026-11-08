from NMX_formal import *
for a,m in [(1086,'BoxEmitted'),(1087,'BoxValue'),(1088,'BoxAction')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
