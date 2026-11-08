from NMX_formal import *
for a,m in [(1362,'NMX_R8_Head241'),(1363,'NMX_R8_Native241'),(1364,'NMX_R8_Live241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
