"""Final read-only verification of retained exports and newly produced audit artifacts."""
from pathlib import Path
import json,hashlib,lzma
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
export=json.loads((B/'NKK_EXPORT.json').read_text())
assert export['files']
for row in export['files']:
 p=Path(row['path']);assert p.is_file() and p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row
raw=lzma.decompress((B/'NKK_CLOSURE_PINS.json.xz').read_bytes())
assert hashlib.sha256(raw).hexdigest()==(B/'NKK_CLOSURE_PINS.json.sha256').read_text().strip()
closure=json.loads(raw)
for name,row in closure.items():
 p=Path(name);assert p.is_file() and sha(p)==row['sha256'],name
roots=json.loads((B/'NKK_AUDIT_ROOTS.json').read_text());results=[];manifest=[]
for i,group in enumerate(roots['groups']):
 p=B/('NKK_audit/batch10/proof10.json' if i==10 else 'NKK_audit/all/proof'+str(i)+'.json')
 r=json.loads(p.read_text());assert r['exit_status']==0,p
 assert [z['root'] for z in r['results']]==group,(p,'exact final source group')
 manifest.append(dict(path=str(p.relative_to(B)),parent_attempt='NKK_L118' if i==10 else 'NKK_L113',sha256=sha(p)))
 results+=r['results']
assert {r['root'] for r in results}==set(roots['roots'])
for r in results:
 assert r['equal'] and set(r['walked_axioms'])<= {'propext','Classical.choice','Quot.sound'},r
(B/'NKK_FINAL_WALK_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
scan=json.loads((B/'NKK_audit/scan/scan.json').read_text());assert scan['exit_status']==0
log=(B/'NKK_audit/scan/scan.log').read_text();assert 'NFN_SCAN_ZERO_DANGLING' in log
retention=json.loads((B/'NKK_RETENTION.json').read_text())
assert retention['cache_deleted'] is False and retention['own_bytes']<30_000_000_000
assert (B/'NKK_target').is_dir()
report=dict(status='PASS',export_objects=len(export['files']),closure_objects=len(closure),raw_roots=len(results),scan_exit=0,cache_retained=True,keys_touched=False,full_manifest_replayed=False,cargo_target=str(B/'NKK_target'))
(B/'NKK_EXPORT_VERIFY.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
