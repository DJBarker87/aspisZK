from NMX_formal import *
names=['RegistryPureLeaf2','EntryV2Guard','RegistryEntry1Check','RegistryEntry1Value','RegistryEntry2Check','RegistryEntry2Value','RegistryLeafCanonical']
for i,n in enumerate(names,972):
 r=run('NMX_L'+str(i),'lean','NMX_R3_'+n)
 assert r['exit_status']==0
