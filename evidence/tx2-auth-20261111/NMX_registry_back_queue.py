from NMX_formal import *
names=['RegistryFold17','RegistryLeaf2Canonical','RegistryDecoder016','RegistryDecoder012','RegistryDecoder008','RegistryDecoder003']
for i,n in enumerate(names,991):
 r=run('NMX_L'+str(i),'lean','NMX_R3_'+n)
 assert r['exit_status']==0
