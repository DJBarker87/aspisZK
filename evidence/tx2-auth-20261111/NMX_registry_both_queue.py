from NMX_formal import *
names=['RegistryFold13','RegistryFold12','RegistryGuard6','RegistryFold10','RegistryFold9','RegistryFold8','RegistryFold7','RegistryBoolFive','RegistryPrefix0','RegistryBranch1']
for i,n in enumerate(names,1013):
 r=run('NMX_L'+str(i),'lean','NMX_R3_'+n)
 assert r['exit_status']==0
