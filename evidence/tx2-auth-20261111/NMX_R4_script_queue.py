from NMX_formal import *
for a,g in enumerate(range(5,-1,-1),1091):
 r=run('NMX_L'+str(a),'lean','NMX_R4_CallScript'+str(g).zfill(2))
 assert r['exit_status']==0
