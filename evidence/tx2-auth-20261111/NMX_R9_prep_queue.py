from NMX_formal import *
for a,m in [(1365,'NMX_R9_Children241'),(1366,'NMX_R9_After241'),(1367,'NMX_R9_GroupHead241'),(1368,'NMX_R9_HeaderFactor241'),(1369,'NMX_R9_ArgsNative241'),(1370,'NMX_R9_ValidateUse241'),(1371,'NMX_R9_RelReplay241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
