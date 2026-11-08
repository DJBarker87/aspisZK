from NMX_formal import *
for a,m in [(1380,'NMX_R9_Live241'),(1381,'NMX_R9_Args241'),(1382,'NMX_R9_StageTwo')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
