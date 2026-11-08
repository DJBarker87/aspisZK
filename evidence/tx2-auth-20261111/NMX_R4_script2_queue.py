from NMX_formal import *
for a,m in [(1094,'CallScript03'),(1095,'CallScript02'),(1096,'CallScript01'),(1097,'CallScript00'),(1098,'CallRun'),(1099,'ObsLaws')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
