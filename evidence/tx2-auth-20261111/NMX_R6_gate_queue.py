from NMX_formal import *
for a,m in [(1236,'NMX_R6_NativeLeft242'),(1237,'NMX_R6_SourceExact242'),(1238,'NMX_R6_CandidateCombined')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
