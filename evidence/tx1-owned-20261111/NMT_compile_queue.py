from NMT_formal import *
for n,m in [(6,'NMT_first.Funs'),(7,'NMT_stage1_owned.TypesExternal'),(8,'NMT_stage1_owned.Types'),(9,'NMT_stage1_owned.Funs'),(10,'NMT_Outcome'),(11,'NMT_RowSpec_087'),(12,'NMT_RowSpec_094')]:
 r=run(f'NMT_L{n:03}','lean',m)
 if r['exit_status']:break
