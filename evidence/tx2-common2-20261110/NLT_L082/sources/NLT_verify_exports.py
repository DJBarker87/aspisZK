"""Read-only independent verification of exports, pins and audit receipts."""
from pathlib import Path
import json,lzma,hashlib
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((B/'NLT_EXPORT.json').read_text());assert x['files']
for row in x['files']:
 p=Path(row['path']);assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],p
raw=lzma.decompress((B/'NLT_CLOSURE_PINS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(B/'NLT_CLOSURE_PINS.json.sha256').read_text().strip()
closure=json.loads(raw)
for row in closure['selected_objects']:
 p=Path(row['path']);assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],p
prior=json.loads((B/'NLT_PREDECESSOR_COMPARISON.json').read_text());assert prior['status']=='PASS' and not prior['mismatches']
roots=json.loads((B/'NLT_AUDIT_ROOTS.json').read_text())['roots'];results=[]
for p in sorted((B/'NLT_audit').glob('batch*/proof*.json')):
 r=json.loads(p.read_text());assert r['exit_status']==0;results+=r['results']
assert len(results)==len(roots) and {r['root'] for r in results}==set(roots)
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
for mode in ['fixtures','scanfixtures']:
 r=json.loads((B/'NLT_audit'/mode/'fixtures.json').read_text());assert r['exit_status']==0 and len(r['results'])==8
 assert all(r['equal'] for r in r['results'])
 assert [x['walked_axioms'] for x in r['results']]==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
scan=json.loads((B/'NLT_audit/scan/scan.json').read_text());assert scan['exit_status']==0
assert 'NFN_SCAN_ZERO_DANGLING' in (B/'NLT_audit/scan/scan.log').read_text()
cleanup=json.loads((B/'NLT_CLEANUP.json').read_text());assert cleanup['deletions']==0 and not cleanup['cache_deleted']
r=dict(status='PASS',export_objects=len(x['files']),closure_objects=len(closure['selected_objects']),raw_roots=len(results),predecessor_objects=prior['previous_files'],scan_exit=0,cache_retained=True,keys_touched=False,full_manifest_replayed=False)
(B/'NLT_EXPORT_VERIFY.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
