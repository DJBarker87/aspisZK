from NMX_formal import *
for a,m in [(1096,'CallScript02'),(1097,'CallScript01'),(1098,'CallScript00'),(1099,'CallRun'),(1100,'ObsLaws'),(1101,'CallLaws'),(1102,'TryObservation'),(1103,'ObservedStep')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
