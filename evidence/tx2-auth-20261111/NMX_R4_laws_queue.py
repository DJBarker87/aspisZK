from NMX_formal import *
for a,m in [(1101,'ObsLaws'),(1102,'CallLaws'),(1103,'TryObservation'),(1104,'ObservedStep'),(1105,'PdaObservation')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
