from NMX_formal import *
for a,m in [(1115,'Observed04'),(1116,'Observed03'),(1117,'Observed02'),(1118,'Observed01'),(1119,'Observed00'),(1120,'CallRoot'),(1121,'SourceFold'),(1122,'BoxBinding'),(1123,'Authentication')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
 if m=='Authentication':print('CANDIDATE_EXISTS_COMMIT_IMMEDIATELY',flush=True)
