from NMX_formal import *
for a,m in [(1308,'NMX_R8_MagicCheck'),(1309,'NMX_R8_SimulatesPath'),(1310,'NMX_R8_Children241'),(1311,'NMX_R8_GroupSource241'),(1312,'NMX_R8_Std241'),(1313,'NMX_R8_Indexes241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
