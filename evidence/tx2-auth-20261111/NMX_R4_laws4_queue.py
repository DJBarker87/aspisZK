from NMX_formal import *
for a,m in [(1107,'ObservedStep'),(1108,'PdaObservation'),(1109,'CallContext'),(1110,'Observed05')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
