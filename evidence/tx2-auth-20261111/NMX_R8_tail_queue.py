from NMX_formal import *
for a,m in [(1348,'NMX_R8_RelReplay241'),(1349,'NMX_R8_Encoded241'),(1350,'NMX_R8_ReadsFactor241'),(1351,'NMX_R8_Reads241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
