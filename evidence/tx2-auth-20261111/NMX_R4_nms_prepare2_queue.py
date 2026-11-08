from NMX_formal import *
for a,m in [(1144,'NMSCarrier'),(1145,'NMS233')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
