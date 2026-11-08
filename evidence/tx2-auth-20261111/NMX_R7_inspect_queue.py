from NMX_formal import *
for a,m in [(1245,'NMX_R7_Std241'),(1246,'NMX_R7_Error241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
