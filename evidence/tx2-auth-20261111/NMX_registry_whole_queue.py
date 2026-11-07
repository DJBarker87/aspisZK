from NMX_formal import *
names=['RegistryFold6','RegistryFold5','RegistryFold4','RegistryFold3','RegistryBranch2','RegistryBranches','RegistryPrefix1','RegistryPolicy','RegistryTop','RegistryObserve']
for i,n in enumerate(names,1023):
 r=run('NMX_L'+str(i),'lean','NMX_R3_'+n)
 assert r['exit_status']==0
