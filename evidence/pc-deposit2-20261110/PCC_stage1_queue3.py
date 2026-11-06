from PCC_formal import *
for a,m in [(16,'PCC_ErrorTransport'),(17,'PCC_ErrorBind'),(18,'PCC_Scalar'),(19,'PCC_ZeroedReference'),(20,'PCC_FreshReference'),(21,'PCC_InfosReference')]:
 r=run(f'PCC_L{a:03d}','lean',m)
 if r['exit_status']!=0:break
