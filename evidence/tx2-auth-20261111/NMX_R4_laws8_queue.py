from NMX_formal import *
for a,m in [(1112,'PdaObservation'),(1113,'CallContext'),(1114,'Observed05')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
