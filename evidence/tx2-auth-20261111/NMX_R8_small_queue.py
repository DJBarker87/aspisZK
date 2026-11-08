from NMX_formal import *
for a,m in [(1314,'NMX_R8_Std241'),(1315,'NMX_R8_Factor241'),(1316,'NMX_R8_Indexes241'),(1317,'NMX_R8_MapBind'),(1318,'NMX_R8_ScalarContext')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
