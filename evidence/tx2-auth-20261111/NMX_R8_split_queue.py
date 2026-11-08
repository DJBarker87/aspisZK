from NMX_formal import *
for a,m in [(1326,'NMX_R8_MapBind'),(1327,'NMX_R8_ScalarContext'),(1328,'NMX_R8_GroupEncode241'),(1329,'NMX_R8_GroupReads241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
