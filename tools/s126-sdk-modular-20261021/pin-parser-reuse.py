#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';O=B/'evidence/s126-current-caller-20261021/reused-parser';O.mkdir(exist_ok=True)
rev='e5a601bea1d808531dbc296ae120b6886a4a9e68';name='MultiproofConeVecLaws';base='docs/research/100bit-spend-path-20261013/'
sha=lambda b:hashlib.sha256(b).hexdigest()
source=subprocess.check_output(['git','-C',str(R),'show',rev+':'+base+'lean/'+name+'.lean'])
receipt=subprocess.check_output(['git','-C',str(R),'show',rev+':'+base+'evidence/multiproof-cone-20261021/'+name+'-6/receipt.json'])
j=json.loads(receipt);obj=Path('/tmp/codex-cx-multiproof-cone-20261021-objects')/(name+'.olean')
assert sha(source)==j['source_sha256'];assert sha(obj.read_bytes())==j['object_sha256']
(O/(name+'.lean.txt')).write_bytes(source);(O/(name+'-receipt.json')).write_bytes(receipt)
(O/'pin.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',revision=rev,source_path=base+'lean/'+name+'.lean',source_sha256=sha(source),object_path=str(obj),object_sha256=sha(obj.read_bytes()),used=['clone_bytes','to_vec_bytes'],qualification='Read-only reuse of the landed parser cone and its warm cache. No sibling source or object modified. Source retained as text, no compiled object distributed.'),indent=2)+'\n')
