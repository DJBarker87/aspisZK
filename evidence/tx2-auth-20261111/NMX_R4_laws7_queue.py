from NMX_formal import *
for a,m in [(1111,'PdaObservation'),(1112,'CallContext'),(1113,'Observed05')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
