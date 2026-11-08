from NMX_formal import *
for a,m in [(1168,'Size242'),(1169,'PrefixSource242'),(1170,'Native242')]:
 r=run('NMX_L'+str(a),'lean','NMX_R5_'+m)
 assert r['exit_status']==0
