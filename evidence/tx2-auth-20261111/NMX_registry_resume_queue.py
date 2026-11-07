from NMX_formal import *
for a,m in [('NMX_L945','NMX_R3_RegistryErasureTail'),('NMX_L946','NMX_R3_RegistryEffects')]:
 r=run(a,'lean',m);assert r['exit_status']==0
