from NLF_formal import run
for i,m in [(11,'NLF_Admission'),(12,'NLF_ParentModel'),(13,'NLF_Invariant'),(14,'NLF_AcquireInvariant'),(15,'NLF_ReleaseInvariant')]:
 r=run(f'NLF_L{i:03d}','lean',m)
 if r['exit_status']:break
