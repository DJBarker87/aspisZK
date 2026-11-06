from NLF_formal import run
for i,m in [(23,'NLF_SnapshotEvents'),(24,'NLF_SnapshotFold'),(25,'NLF_SevenAccounts')]:
 r=run(f'NLF_L{i:03d}','lean',m)
 if r['exit_status']:break
