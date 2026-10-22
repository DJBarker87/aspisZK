#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
h=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((root/'source-pins.json').read_text())
manifest=json.loads((root/'manifest.json').read_text())
assert manifest['schema']=='s4-checked-q-all-unrolled-candidate-v1'
listed={x['path'] for x in manifest['files']}
actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p.name!='manifest.json'}
assert listed==actual
for x in manifest['files']:
 p=root/x['path']; assert p.is_file() and p.stat().st_size==x['bytes'] and h(p)==x['sha256']
orig=root/'source-snapshot/fast_pairing.original.rs'
cand=root/'source-snapshot/fast_pairing.candidate.rs'
old='pub fn from_limbs(x:[u32;4])->Option<Self>{if x.iter().all(|&v|v<P){Some(Self(x))}else{None}}'
new='''pub fn from_limbs(x:[u32;4])->Option<Self>{
            let [a,b,c,d]=x;
            if a<P && b<P && c<P && d<P {Some(Self([a,b,c,d]))}else{None}
        }'''
a=orig.read_text(); b=cand.read_text()
assert h(orig)==pins['original_source_sha256']
assert h(cand)==pins['candidate_source_sha256']
assert a.count(old)==1
assert a.replace(old,new)==b, 'candidate differs outside the one validated method replacement'
assert old not in b and b.count(new)==1
compact=lambda s: ''.join(s.split())
predicate='a<P&&b<P&&c<P&&d<P'
assert predicate in compact(b)
test_text=(root/'tests/iterator_all_equivalence.rs').read_text()
assert predicate in compact(test_text), 'differential harness must test the same ordered predicate'
assert 'x.iter().all(|&v| v < P)' in test_text, 'test must compare with the std Iterator::all reference'
assert 'canonical::Q::from_limbs(limbs_of(k)).ok_or(())' in a
assert 'canonical::Q::from_limbs(limbs_of(k)).ok_or(())' in b
patch=(root/'candidate.patch').read_text()
assert patch, 'missing visible diff'
test=root/'tests/iterator_all_equivalence.rs'
assert h(test)==pins['test_source_sha256']
receipt=json.loads((root/'tests/receipt.json').read_text())
assert receipt['exit_status']==0 and receipt['result']=='2 passed, 0 failed'
assert h(root/receipt['run_log'])==receipt['run_log_sha256']
assert h(root/receipt['time_log'])==receipt['time_log_sha256']
print('PASS: exact one-method replacement, unchanged checked_q call, frozen source pins, and test input pin')
