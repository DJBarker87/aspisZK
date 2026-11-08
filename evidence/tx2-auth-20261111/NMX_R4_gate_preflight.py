from NMX_formal import *
for a,m in [(1130,'BoxCoverage'),(1131,'CandidateCombined')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
