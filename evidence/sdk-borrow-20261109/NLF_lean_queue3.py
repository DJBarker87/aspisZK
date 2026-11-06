from NLF_formal import run
for i,m in [(32,'NLF_CounterLaws'),(33,'NLF_ExclusiveBracket'),(34,'NLF_ThreeAccounts'),(35,'NLF_InitialBinding'),(36,'NLF_EntrySnapshot'),(37,'NLF_CopyStep'),(38,'NLF_ProgramFold'),(39,'NLF_FlagSemantics')]:
 r=run(f'NLF_L{i:03d}','lean',m)
 if r['exit_status']:break
