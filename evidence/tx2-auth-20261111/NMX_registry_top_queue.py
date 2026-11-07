from NMX_formal import *
for i,n in enumerate(['RegistryPrefix1','RegistryPolicy','RegistryTop','RegistryObserve','RegistryByteCut'],1031):
 r=run('NMX_L'+str(i),'lean','NMX_R3_'+n)
 assert r['exit_status']==0
