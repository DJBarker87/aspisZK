"""Replay the prior random/grid corpus byte-for-byte on the new frozen ELF.
Random witness and OS-mask generation is inherited, never replaced with public seeds.
"""
import json,sys
from pathlib import Path
H=Path(sys.argv[1]); O=H.parent/'codex-cx-cu-bound3-20261020'
for name in ['variants','variants-extra','targeted','random-a','random-b']:
 p=json.loads((O/f'plan-{name}.json').read_text()); oldout=Path(p['out'])
 for r in p['runs']:
  a=r['args']; i=a.index('--mask-entropy'); del a[i:i+2]
  task=oldout/'runs'/r['label']/'task'
  assert (task/'r1-s2-proof.bin').exists(),task
  a+=['--reuse',str(task/'r1-s2-proof.bin'),str(task/'r1-s2-public-asf8.bin')]
  r['corpus_origin']=str(oldout/r['label'])
 for k in ['driver','pool','verifier','out']:
  p[k]=p[k].replace(str(O),str(H))
 (H/f'plan-{name}.json').write_text(json.dumps(p,indent=1))
print('Pinned prior corpus plans ready; new ELF measurements required for every row.')
