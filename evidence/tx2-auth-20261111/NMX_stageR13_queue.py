from NMX_formal import *
r=run('NMX_L281','lean','NMX_SemanticF03b')
for i,m in enumerate(['NMX_U64Layout','NMX_U64Byte0','NMX_U64Byte1'],282):
 r=run(f'NMX_L{i:03d}','lean',m)
 if r['exit_status']:
  print('STOP dependent byte pipeline on failed predecessor',flush=True);break
