#!/usr/bin/env python3
"""Pin reused arithmetic source/receipts and selected cached import hashes."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';O=E/'reused-checkpoint-size';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
selected=json.loads((E/'selected-import-pins.json').read_text());mods={r['name']:r for r in selected['modules']}
rows=[]
source=B/'lean/R22Stage2LeafTotal.lean';packet=B/'evidence/import-coll-20261021/manifest.json'
record=next(r for r in json.loads(packet.read_text())['attempts'] if r.get('module')=='R22Stage2LeafTotal')
assert record['source_sha256']==sha(source) and record['exit']==0 and record['swaps']==0
rows.append(('R22Stage2LeafTotal',source,packet,record))
source=B/'lean-candidates/actual-heap-final-length-20261019/Tx1FinalLenBoundV8.lean'
packet=B/'evidence/tx1-actual-filled-final-length-20261019/evidence/tx1-final-len-bound-v8/receipt.json';record=json.loads(packet.read_text())
assert record['source_sha256']==sha(source) and record['exit_status']==0 and record['process_swap_count']==0
assert record['object_sha256']==mods['Tx1FinalLenBoundV8']['sha256']
rows.append(('Tx1FinalLenBoundV8',source,packet,record))
manifest=[]
for module,source,packet,record in rows:
 (O/(module+'.lean')).write_bytes(source.read_bytes())
 (O/(module+'-receipt.json')).write_text(json.dumps(record,indent=2)+'\n')
 manifest.append(dict(module=module,source_path=str(source.relative_to(R)),source_sha256=sha(source),receipt_path=str(packet.relative_to(R)),receipt_sha256=sha(packet),cached_object=mods[module]))
(O/'pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',qualification='Unchanged successful arithmetic proofs reused; fresh S2SdkCheckpointSizeTotalV1 identities connect the exact emitted functions to these checked definitions. Current cached objects/imports pinned separately from historical receipt metadata. Final coherent source replay still required.',imports=manifest),indent=2)+'\n')
print('PASS exact reused source hashes and successful historical receipts; selected object pins recorded')
