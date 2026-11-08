from NMX_formal import *
for a,m in [(1274,'NMX_R7_VerifierSource241'),(1275,'NMX_R7_RelVerify241'),(1276,'NMX_R7_RelPublic241'),(1277,'NMX_R7_RelReads241'),(1278,'NMX_R7_RelValidate241'),(1279,'NMX_R7_MagicNe241'),(1280,'NMX_R8_Code241')]:
 r=run('NMX_L'+str(a),'lean',m)
 assert r['exit_status']==0
