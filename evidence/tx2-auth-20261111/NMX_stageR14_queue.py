from NMX_formal import *
r=run('NMX_L285','lean','NMX_UIntApi')
for i,m in enumerate([f'NMX_U64Byte{k}' for k in range(2,8)],286):
 r=run(f'NMX_L{i:03d}','lean',m)
 if r['exit_status']:
  print('STOP symbolic-byte class after failed predecessor',flush=True);break
