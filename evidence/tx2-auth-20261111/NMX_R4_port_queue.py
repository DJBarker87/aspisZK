from NMX_formal import *
for a,m in [(1083,'ArgsPort'),(1084,'AllArgs')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
