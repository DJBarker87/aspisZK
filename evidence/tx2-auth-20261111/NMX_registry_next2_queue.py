from NMX_formal import *
for i,n in enumerate(['RegistryLeafCanonical','RegistryPdaLaw','RegistryProtocols','RegistryDecoderLaw','RegistryPda17'],983):
 r=run('NMX_L'+str(i),'lean','NMX_R3_'+n)
 assert r['exit_status']==0
