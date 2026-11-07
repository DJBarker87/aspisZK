from NMX_formal import *
names=['RegistryGuard14','RegistryFold14','RegistryPda010','RegistryPda005']
for i,n in enumerate(names,1007):
 r=run('NMX_L'+str(i),'lean','NMX_R3_'+n)
 assert r['exit_status']==0
