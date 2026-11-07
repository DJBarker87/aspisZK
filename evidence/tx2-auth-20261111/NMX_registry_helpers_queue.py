from NMX_formal import *
names=['RegistryCarrier','RegistryOps','RegistryStd','RegistryScalarOps','RegistryFlagValues','RegistryArgs','RegistryRecordGuards','EntryRecordGuards']
for i,n in enumerate(names,963):
 r=run('NMX_L'+str(i),'lean','NMX_R3_'+n)
 assert r['exit_status']==0
