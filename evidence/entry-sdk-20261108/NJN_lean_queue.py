from NJN_formal import *
for i,m in [(5,'NJN_AcquireLaws'),(6,'NJN_DropLaws'),(7,'NJN_CopyLaws'),(8,'NJN_ClockModel'),(9,'NJN_PdaModel')]:
 run(f'NJN_L{i:03d}','lean',m)
