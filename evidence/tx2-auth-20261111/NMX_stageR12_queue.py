from NMX_formal import *
for i,m in enumerate(['NMX_LEFirst','NMX_U64Layout','NMX_U64Byte0','NMX_U64Byte1'],276):
 r=run(f'NMX_L{i:03d}','lean',m)
 if r['exit_status']:
  print('STOP dependent byte pipeline on failed predecessor',flush=True);break
r=run('NMX_L280','lean','NMX_NecessaryConditions')
