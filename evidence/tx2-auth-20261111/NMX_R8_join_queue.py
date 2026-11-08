from NMX_formal import *
for a,m in [(1356,'NMX_R8_Reads241'),(1357,'NMX_R8_AfterFactor241'),(1358,'NMX_R8_After241'),(1359,'NMX_R8_RawPath241'),(1360,'NMX_R8_ValidateUse241'),(1361,'NMX_R8_HeaderFactor241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
