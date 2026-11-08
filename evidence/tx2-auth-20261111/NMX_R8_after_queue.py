from NMX_formal import *
for a,m in [(1352,'NMX_R8_ReadsFactor241'),(1353,'NMX_R8_Reads241'),(1354,'NMX_R8_AfterFactor241'),(1355,'NMX_R8_After241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
