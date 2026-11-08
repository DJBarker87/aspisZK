from NMX_formal import *
for a,m in [(1109,'PdaObservation'),(1110,'CallContext'),(1111,'Observed05')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
