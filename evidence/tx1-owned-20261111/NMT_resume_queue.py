from NMT_formal import run
for n,m in [(86,'NMT_345CheckpointData'),(87,'NMT_345ZeroRange'),(88,'NMT_345ZeroInduction')]:
 r=run(f'NMT_L{n:03}','lean',m)
 if r['exit_status']:break
