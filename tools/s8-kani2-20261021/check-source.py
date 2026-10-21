#!/usr/bin/env python3
"""Check exact retained model reuse and literal frozen Rust includes."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s8-kani2-20261021'
subprocess.run(['python3',str(R/'tools/s8-kani-20261021/generate.py'),'--check'],check=True)
reuse=json.loads((E/'mutable-source-reuse.json').read_text())
mapping={str(Path(d['retained_source']).with_suffix('')).split('/sources/')[1].replace('/','.'):name for name,d in reuse.items()}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def executable_tokens(s):
 s=re.sub(r'^#print axioms [^\n]+','',s,flags=re.M)
 return s.split()
for name,d in reuse.items():
 source=R/d['retained_source'];assert sha(source)==d['sha256']
 expected=source.read_text()
 for old,new in mapping.items():expected=expected.replace('import '+old,'import '+new)
 if name=='S8Kani2PendingWrite':expected+='\nend batched_weights\nend AspisR1BatchedWeightsFinishExtraction\n'
 actual=B/'lean'/(name+'.lean')
 assert executable_tokens(expected)==executable_tokens(actual.read_text()),name
source=(R/'tools/s8-kani2-20261021/src/lib.rs').read_text()
assert 'include!("../../s8-kani-20261021/src/frozen.rs");' in source
assert 'include!("../../s8-kani-20261021/src/owned.rs");' in source
selected=(R/'tools/s8-kani2-20261021/src/selected.rs').read_text()
assert '*w=pending.value(i);' in selected and 'reference[cursor]=value_owned(rows[cursor]);' in selected
assert 'let row:[u64;4]=kani::any();let rows=[row;64];' in selected
assert 'let i=cursor+relative;' in selected and 'assert_eq!(i,cursor);' in selected
pins={str(p.relative_to(R)):sha(p) for root in [R/'tools/s8-kani2-20261021',B/'lean'] for p in root.rglob('*') if p.is_file() and (root.name!='lean' or p.name.startswith('S8Kani2')) and '__pycache__' not in p.parts}
out={'frozen_source_binding':'../s8-kani-20261021/source-binding.json','reused_models':reuse,'pins':pins,'interpretation':'Kani next on related suffix/cursor state, selected raw row arbitrary; Lean value_reference supplies arbitrary raw-vector read equality. The exact unsafe stdlib-to-opaque-IterMut representation remains a P6 model boundary, not a kernel extraction theorem.'}
(E/'source-binding.json').write_text(json.dumps(out,indent=2)+'\n');print('Frozen Rust includes and all retained mutable-model transformations match')
