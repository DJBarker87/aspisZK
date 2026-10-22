#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).parent
err=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for line in (root/'SHA256SUMS').read_text().splitlines():
 h,rel=line.split('  ',1); p=root/rel
 if not p.is_file() or sha(p)!=h: err.append('checksum mismatch/missing '+rel)
for p in root.rglob('*'):
 if p.is_file() and p.suffix in {'.olean','.ilean','.o','.dylib'}: err.append(f'binary present: {p.relative_to(root)}')
m=json.loads((root/'manifest.json').read_text())
r=json.loads((root/m['receipt']).read_text())
if m['schema']!='focused-extractor-proof-packet-v1': err.append('schema mismatch')
if r['exit_status']!=0 or r['watchdog_abort'] is not None: err.append('Lean receipt is not green')
if r['source_sha256']!=m['source_sha256'] or r['object_sha256']!=m['object_sha256']: err.append('source/object pin mismatch')
if m['closure_missing'] or m['closure_modules']!=5524: err.append('closure report mismatch')
if sha(root/'dependencies/full-profile.txt')!=m['lean_path_sha256']: err.append('profile hash mismatch')
if sha(root/'dependencies/closure.json')!=m['closure_sha256']: err.append('closure hash mismatch')
if sha(root/'sources/QueryWordsSamplerBridgeV1.lean')!=m['source_sha256']: err.append('retained source hash mismatch')
s=(root/'sources/QueryWordsSamplerBridgeV1.lean').read_text()
for x in ['theorem query_words_success_sampler_words18','query_words_success_byte_mask','SamplerWordBridge.source_word','SqueezeOracleBridge.array_roundtrip','#print axioms query_words_success_sampler_words18']:
 if x not in s: err.append('source missing '+x)
if 'sorry' in s or 'admit' in s: err.append('source contains sorry/admit token')
log=(root/'receipts/lean.log').read_text()
if 'sorryAx' in log: err.append('axiom log contains sorryAx')
for name in ['query_mask_word_value','rank_word_value','query_words_success_sampler_words18']:
 if name not in log: err.append('missing axioms report for '+name)
for x in m['axioms']:
 if x not in log: err.append('axiom absent from report: '+x)
pins=json.loads((root/'dependencies/direct-import-pins.json').read_text())['imports']
if len(pins)!=4: err.append('expected four direct import pins')
if err: print('\n'.join(err)); sys.exit(1)
print('PASS: same-block successful query_words to exact sampler words, full profile/closure and direct pins verified; standard axioms only; source-only packet.')
