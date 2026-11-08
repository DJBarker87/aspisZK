from NMX_formal import *
for a,m in [(1334,'NMX_R8_EncoderUse241'),(1335,'NMX_R8_VerifierUse241'),(1336,'NMX_R8_Digest241'),(1337,'NMX_R8_GroupValidate241'),(1338,'NMX_R8_GroupHead241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
