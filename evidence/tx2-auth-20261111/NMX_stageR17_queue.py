from NMX_formal import *
r=run('NMX_L304','lean','NMX_RSNormalize')
if r['exit_status']==0:r=run('NMX_L305','lean','NMX_CanonicalBodyFactor')
for i,m in enumerate(['NMX_SemanticF03a','NMX_SemanticF02','NMX_SemanticF01','NMX_SemanticF00'],306):
 r=run(f'NMX_L{i:03d}','lean',m)
 if r['exit_status']:
  print('STOP semantic pipeline on failed predecessor',flush=True);break
