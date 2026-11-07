from NMX_formal import *
names=['RegistryData015','RegistryData007','RegistryPda009','RegistryPda013','RegistryPda004','RegistryFold15','RegistryReadonly','RegistryGuard14']
for i,n in enumerate(names,999):
 r=run('NMX_L'+str(i),'lean','NMX_R3_'+n)
 assert r['exit_status']==0
