from NMX_formal import *
for a,m in [(1141,'NMSFold242'),(1142,'NMS242Instantiation'),(1143,'NMSCarrier'),(1144,'NMS233')]:
 r=run('NMX_L'+str(a),'lean','NMX_R4_'+m)
 assert r['exit_status']==0
