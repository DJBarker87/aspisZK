from NMX_formal import *
for i,m in enumerate(['NMX_InspectLE','NMX_SeedConstants','NMX_CheckTransport','NMX_SyntaxFactor','NMX_TailIndependent'],264):
 r=run(f'NMX_L{i:03d}','lean',m)
 if r['exit_status']:
  print('STOP required predecessor failed',flush=True);break
