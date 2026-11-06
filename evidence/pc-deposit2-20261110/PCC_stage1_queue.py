from PCC_formal import *
for a,m in [(10,'PCC_Reference'),(11,'PCC_Shared'),(12,'PCC_BasicReferences'),(13,'PCC_RuntimeCpiAccountView')]:
 r=run(f'PCC_L{a:03d}','lean',m)
 if r['exit_status']!=0:break
