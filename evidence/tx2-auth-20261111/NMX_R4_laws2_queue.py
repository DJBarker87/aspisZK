from NMX_formal import *
for a,m in [(1103,'CallLaws'),(1104,'TryObservation'),(1105,'ObservedStep'),(1106,'PdaObservation'),(1107,'CallContext'),(1108,'Observed05')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
