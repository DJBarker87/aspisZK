#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for line in (D/'SHA256SUMS').read_text().splitlines():
 h,f=line.split('  ',1);assert sha(D/f)==h,f
m=json.loads((D/'manifest.json').read_text());assert m['schema']=='focused-extractor-proof-packet-v1'
for target in m['modules']:
 assert sha(D/target['source'])==target['source_sha256']
 receipt=json.loads((D/target['receipt']).read_text());assert receipt['exit_status']==0 and receipt['scope_swap_peak_bytes']==0
 assert receipt['object_sha256']==target['object_sha256']
 ev=(D/target['receipt']).parent;pre=json.loads((ev/'preflight.json').read_text());assert pre['source_sha256']==target['source_sha256']
 assert pre['limits']['memory.swap.max']=='0' and pre['limits']['memory.max']=='2147483648'
 for name,pin in pre['direct_imports'].items():assert m['direct_import_source_map'][name]['object_sha256']==pin['sha256']
 text=(ev/'lean.log').read_text();assert 'sorryAx' not in text
 for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text):assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',axioms))<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',(D/target['source']).read_text())
assert not any(x.suffix in ['.olean','.ilean','.ir','.o','.a','.so','.llbc'] for x in D.rglob('*') if x.is_file())
print('PASS: source/import/receipt hashes, focused caps, standard axioms, source-only packet')
