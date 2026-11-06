from PCC_formal import *
for a,m in [(12,'PCC_Shared'),(13,'PCC_BasicReferences'),(14,'PCC_RuntimeCpiAccountView'),(15,'PCC_ErrorTransport'),(16,'PCC_ErrorBind')]:
 r=run(f'PCC_L{a:03d}','lean',m)
 if r['exit_status']!=0:break
