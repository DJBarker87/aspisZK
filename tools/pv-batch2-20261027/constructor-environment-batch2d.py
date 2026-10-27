"""Regenerate the full constructor environment with qualified carrier readers."""
from pathlib import Path
import sys
from named_discriminants import qualify
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
B=Path('evidence/pv-batch2-20261027/batch2b/drafts')
s=(B/'PV_B2_ConstructorEnvironment.lean.txt').read_text().replace('import R1Z.ProverRwFullTypes\n','')
p=Path('evidence/pv-batch2-20261027/extraction-weights/generated-252/Types.lean')
t=p.read_text().replace('import Aeneas\n','').replace('PV_B2_252','PV_B2_C_Carrier')
s=s.replace('import Aeneas\n','import Aeneas\nsection\n'+t+'\nend\n',1).replace('ProverRwFull.','PV_B2_C_Carrier.')
for n in ['WeightsNative','FieldValue','FieldTotal','ArrayTotal','WeightsTotal']:s=s.replace('PV_B2_'+n,'PV_B2_C_'+n)
s=qualify(s);p=L/'PV_B2_C_ConstructorEnvironment.lean'
if '--check' in sys.argv:assert p.read_text()==s,p
else:p.write_text(s)
