from NMX_formal import *
jobs=[('NMX_L151','NMX_Carrier'),('NMX_L135','NMX_ScalarCarrier'),('NMX_L136','NMX_FreshOwners'),('NMX_L137','NMX_CanonicalErrorPrefix'),('NMX_L138','NMX_KeyCarrier'),('NMX_L139','NMX_ObserveResult'),('NMX_L140','NMX_ReadonlyCarrier'),('NMX_L141','NMX_DataCarrier'),('NMX_L142','NMX_CheckpointCarrier'),('NMX_L143','NMX_InverseBytes'),('NMX_L144','NMX_PrimitiveInstall'),('NMX_L145','NMX_PdaCarrier'),('NMX_L146','NMX_CallArguments'),('NMX_L147','NMX_FoldedProgram'),('NMX_L148','NMX_Question')]
for a,m in jobs:
 r=run(a,'lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
