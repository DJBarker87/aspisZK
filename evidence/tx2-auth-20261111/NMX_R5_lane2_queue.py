from NMX_formal import *
for a,m in [(1150,'Lane242'),(1151,'LaneSource242'),(1152,'Slot242')]:
 r=run('NMX_L'+str(a),'lean','NMX_R5_'+m)
 assert r['exit_status']==0
