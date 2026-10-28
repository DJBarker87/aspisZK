"""Recreate private carrier Types from pinned raw emission, including named readers."""
from pathlib import Path
import re,sys
from named_discriminants import qualify
E=Path('evidence/pv-batch2-20261027/batch2c/batch2c-extraction-1')
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
for op in [251,253]:
 t=(E/f'generated-{op}/Types.lean').read_text()
 s=qualify(t+'\n'+''.join(f'#print axioms PV_B2_{op}c1.{d}\n' for d in re.findall(r'^(?:def|structure|inductive) ([\w.]+)',t,re.M)))
 p=L/f'PV_B2_C_RawWeights{op}Types.lean'
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
