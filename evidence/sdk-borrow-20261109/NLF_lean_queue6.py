from NLF_formal import run
mods=[f'NLF_TX1_Snapshot{i}' for i in range(3)]+[f'NLF_TX2_Snapshot{i}' for i in range(7)]
for i,m in enumerate(mods,54):
 r=run(f'NLF_L{i:03d}','lean',m)
 if r['exit_status']:break
