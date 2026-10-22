#!/usr/bin/env python3
import hashlib,json,pathlib
r=pathlib.Path(__file__).resolve().parent
m=json.loads((r/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(r/m['source']['path'])==m['source']['sha256']
rec=json.loads((r/'evidence/receipt.json').read_text())
assert rec['exit_status']==0 and rec['source_sha256']==m['source']['sha256']
assert rec['object_sha256']==m['object_external_pin']['sha256'] and m['object_external_pin']['not_included'] is True
assert m['compile']['process_swaps']==0 and m['compile']['exit_status']==0
assert sha(r/'evidence/LEAN_PATH.txt')==m['selected_profile']['sha256']
assert sha(r/'evidence/import-closure.json')==m['closure']['sha256']
cl=json.loads((r/'evidence/import-closure.json').read_text())
assert len(cl['owners'])==m['closure']['modules'] and cl['missing']==[]
log=(r/'evidence/lean.log').read_text()
assert "AspisR1S9N4PowerArraySemanticsV1.actual_s9_n4_low_high_arrays_from_canonical' depends on axioms:" in log
assert '[propext,' in log and 'Classical.choice' in log and 'Quot.sound' in log and 'sorryAx' not in log
for p in r.rglob('*'):
 if p.is_file() and p.suffix in {'.olean','.ilean','.c','.o','.a','.so','.dylib'}: raise AssertionError(f'compiled artifact included: {p}')
files=sorted(p for p in r.rglob('*') if p.is_file() and p.name!='SHA256SUMS')
(r/'SHA256SUMS').write_text(''.join(f'{sha(p)}  {p.relative_to(r)}\n' for p in files))
for line in (r/'SHA256SUMS').read_text().splitlines():
 h,rel=line.split('  ',1); assert sha(r/rel)==h,rel
print('S9 N=4 power-array packet PASS')
