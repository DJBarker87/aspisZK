from NMX_formal import *
for a,m in [(1149,'Lane242'),(1150,'LaneSource242')]:
 r=run('NMX_L'+str(a),'lean','NMX_R5_'+m)
 assert r['exit_status']==0
