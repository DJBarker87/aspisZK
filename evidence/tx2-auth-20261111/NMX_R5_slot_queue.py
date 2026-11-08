from NMX_formal import *
for a,m in [(1153,'Slot242'),(1154,'Guards242')]:
 r=run('NMX_L'+str(a),'lean','NMX_R5_'+m)
 assert r['exit_status']==0
