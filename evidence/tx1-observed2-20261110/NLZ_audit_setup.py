from pathlib import Path
import json,hashlib
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in json.loads((B/'NLZ_AUDIT_MANIFEST_PINS.json').read_text()).items():assert sha(B/n)==h,n
walker=json.loads((B/'NLZ_WALKER_PINS.json').read_text());assert walker['byte_identical']and sha(B/'NLZ_WALKER.lean.txt')==walker['source_sha256']
for r in walker['selected_objects']:assert sha(Path(r['path']))==r['sha256']
m=json.loads((B/'NLZ_MODULES.json').read_text());rows=[]
for name,receipt in m['selected_receipts'].items():
 r=json.loads((B/receipt).read_text());n='NLZ_generated/'+name+'.lean';p=B/n;q=(B/receipt).parent/'sources'/n
 assert r['exit_status']==0 and sha(p)==sha(q)==r['source_hashes'][n]
 rows.append(dict(module=name,path=str(p),sha256=sha(p),receipt=receipt,revision=r['source_revision']))
(B/'NLZ_PROOF_SOURCE.json').write_text(json.dumps(dict(sources=rows),indent=2))
print(json.dumps(dict(status='READY_FOR_ONE_COMBINED_AUDIT',sources=len(rows),positive_row_roots=[],target_established=False)))
