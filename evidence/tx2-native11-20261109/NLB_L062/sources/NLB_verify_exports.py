"""Final read-only verification of retained exports and newly produced audit artifacts."""
from pathlib import Path
import json,hashlib,lzma
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
export=json.loads((B/'NLB_EXPORT.json').read_text())
assert export['files']
for row in export['files']:
 p=Path(row['path']);assert p.is_file() and p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row
raw=lzma.decompress((B/'NLB_CLOSURE_PINS.json.xz').read_bytes())
assert hashlib.sha256(raw).hexdigest()==(B/'NLB_CLOSURE_PINS.json.sha256').read_text().strip()
closure=json.loads(raw)
for name,row in closure.items():
 p=Path(name);assert p.is_file() and sha(p)==row['sha256'],name
roots=json.loads((B/'NLB_AUDIT_ROOTS.json').read_text())['roots'];results=[]
for p in sorted((B/'NLB_audit').glob('batch*/proof*.json')):
 r=json.loads(p.read_text());assert r['exit_status']==0,p
 results+=r['results']
assert {r['root'] for r in results}==set(roots)
for r in results:
 assert r['equal'] and set(r['walked_axioms'])<= {'propext','Classical.choice','Quot.sound'},r
for mode in ['fixtures','scanfixtures2']:
 fixture=json.loads((B/'NLB_audit'/mode/'fixtures.json').read_text())
 assert fixture['exit_status']==0 and len(fixture['results'])==8
 assert all(r['equal'] for r in fixture['results'])
 assert [r['walked_axioms'] for r in fixture['results']]==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
scan=json.loads((B/'NLB_audit/scan/scan.json').read_text());assert scan['exit_status']==0
log=(B/'NLB_audit/scan/scan.log').read_text();assert 'NFN_SCAN_ZERO_DANGLING' in log
cleanup=json.loads((B/'NLB_CLEANUP.json').read_text());assert cleanup['cache_deleted'] is False
assert (B/'NLB_target').exists() and cleanup['retained_target'] is True
report=dict(status='PASS',export_objects=len(export['files']),closure_objects=len(closure),raw_roots=len(results),scan_exit=0,cache_retained=True,keys_touched=False,full_manifest_replayed=False)
(B/'NLB_EXPORT_VERIFY.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
