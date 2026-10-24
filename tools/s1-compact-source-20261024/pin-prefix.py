#!/usr/bin/env python3
"""Pin checked native prefix consumer targets, without replay."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
selected={'S1NativeCompactBodyFrameV1':'s1-native-compact-body-frame-v3','S1NativeCompactLoopFrameV1':'s1-native-compact-loop-frame-v1','S1NativeCompactRootV1':'s1-native-compact-root-v2'}
m=json.loads((E/'accepted-targets.json').read_text())
for n,d in selected.items():
 r=json.loads((E/d/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert hashlib.sha256((S/(n+'.lean')).read_bytes()).hexdigest()==r['source_sha256']
 assert r['print_axioms'] and all('sorryAx' not in x for x in r['print_axioms'])
 m['targets'][n]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][n]['receipt']=d+'/receipt.json'
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
files=[Path(__file__).resolve(),Path(__file__).with_name('check-prefix.py').resolve(),B/'design/S1-NATIVE-COMPACT-PREFIX-20261024.md',E/'s1-native-compact-prefix-import-pins.json']
filepins={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(E/'s1-native-compact-prefix-targets.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','targets':{n:d+'/receipt.json' for n,d in selected.items()},'files':filepins,'qualification':'Actual extracted semantic expansion prefix property, accepted-only, with value leaf arbitrary. Final buffer/parser/caller join remains open.'},indent=2)+'\n')
print('Pinned three checked native prefix targets')
