from NLF_formal import run
for i,m in [(49,'NLF_MetadataLaws'),(50,'NLF_SnapshotOccurrence')]:
 r=run(f'NLF_L{i:03d}','lean',m)
 if r['exit_status']:break
