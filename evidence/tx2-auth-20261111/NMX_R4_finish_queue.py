from NMX_formal import *
for a,m in [(1120,'Observed04'),(1121,'Observed03'),(1122,'Observed02'),(1123,'Observed01'),(1124,'Observed00'),(1125,'CallRoot'),(1126,'SourceFold'),(1127,'BoxBinding'),(1128,'BoxCoverage'),(1129,'Authentication')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
 if m=='Authentication':print('CANDIDATE_EXISTS_COMMIT_IMMEDIATELY',flush=True)
