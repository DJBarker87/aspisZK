from pathlib import Path
import json,hashlib,lzma
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
raw=lzma.decompress((B/'NLE_CLOSURE_PINS.json.xz').read_bytes())
assert hashlib.sha256(raw).hexdigest()==(B/'NLE_CLOSURE_PINS.json.sha256').read_text().strip()
pins=json.loads(raw);changed=[r['path'] for r in pins.values() if sha(Path(r['path']))!=r['sha256']]
exports=json.loads((B/'NLE_EXPORT.json').read_text());changedExports=[r['path'] for r in exports['files'] if sha(Path(r['path']))!=r['sha256']]
modules=json.loads((B/'NLE_MODULES.json').read_text())+['NLE_COMBINED_IMPORT'];sourceChecks=[]
for module in modules:
 source=B/'NLE_generated'/(module+'.lean');h=sha(source);receipts=[]
 for p in B.glob('NLE_L*/receipt.json'):
  row=json.loads(p.read_text())
  if row['kind']=='lean' and row['module']==module and row['exit_status']==0:
   for name,value in row['source_hashes'].items():
    rh=value if isinstance(value,str) else value['sha256']
    if name.endswith('/'+module+'.lean') and rh==h:receipts.append(row['attempt'])
 assert receipts,('No successful current-source compile',module)
 sourceChecks.append(dict(module=module,source_sha256=h,successful_attempts=receipts))
report=dict(changed_closure=changed,changed_exports=changedExports,closure_objects=len(pins),source_checks=sourceChecks,passed=not changed and not changedExports)
(B/'NLE_EXPORT_VERIFY.json').write_text(json.dumps(report,indent=2)+'\n');assert report['passed'],report
walks=[]
for p in (B/'NLE_audit').rglob('proof*.json'):
 row=json.loads(p.read_text());assert row['exit_status']==0
 walks.append(dict(path=str(p),results=row.get('results'),print_axioms=row['print_axioms']))
(B/'NLE_FINAL_WALK_MANIFEST.json').write_text(json.dumps(dict(walks=walks,source_checks=sourceChecks,closure_sha256=hashlib.sha256(raw).hexdigest()),indent=2)+'\n')
print(json.dumps(dict(passed=True,closure_objects=len(pins),modules=len(sourceChecks),walk_batches=len(walks))))
