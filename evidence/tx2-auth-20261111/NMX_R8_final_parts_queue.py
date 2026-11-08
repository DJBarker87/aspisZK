from NMX_formal import *
for a,m in [(1342,'NMX_R8_GroupHead241'),(1343,'NMX_R8_EncodedFactor241'),(1344,'NMX_R8_ProofSlice241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
