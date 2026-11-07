from NMX_formal import *
for i,m in enumerate(['NMX_U64Model','NMX_U64Carrier','NMX_SemanticF03a','NMX_SemanticF02','NMX_SemanticF01','NMX_SemanticF00'],292):
 r=run(f'NMX_L{i:03d}','lean',m)
 if r['exit_status']:
  print('STOP semantic pipeline on failed predecessor',flush=True);break
