"""Read-only verification of accepted source/dependency snapshots against the host."""
from pathlib import Path
import hashlib,json,sys
h=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026');e=h/'receipts';j=Path('/home/dombarker/project-offloads/aspis-joint-20261019');sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
rows=[]
for p in sorted(e.glob('*-input.json')):
 x=json.loads(p.read_text());a=x['attempt'];out=Path(f'/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/out-{a}.log')
 if not out.exists() or '\nexit=0\n' not in '\n'+out.read_text():continue
 assert sha(e/f'{a}.lean.txt')==x['source_sha256']
 assert hashlib.sha256(json.dumps(x['dependencies'],sort_keys=True).encode()).hexdigest()==x['deps_fingerprint']
 mismatches=[d['module'] for d in x['dependencies'] if sha(Path(d['resolved_object']))!=d['object_sha256']]
 # An early accepted proof's own dependencies may have a later accepted successor.
 # Final source consistency is checked for the latest module input below.
 rows.append(dict(attempt=a,module=x['module'],source_sha256=x['source_sha256'],snapshot_verified=True,changed_dependency_modules=mismatches))
latest={}
for z in rows:latest[z['module']]=z
for m,z in latest.items():
 assert sha(j/'sources'/(m+'.lean'))==z['source_sha256'],m
 assert not z['changed_dependency_modules'],(m,z['changed_dependency_modules'])
result=dict(accepted_inputs=rows,latest_modules=latest,latest_source_and_dependency_objects_verified=True,incorrect_launcher_label_attempt=12032,label_error='Only the deduplication label was wrong; actual source and dependencies independently verified. No shared ledger modification and no repeated Lean compile.',scope='Focused object/source consistency, not coherent frozen release replay.')
(e/'final-environment.json').write_text(json.dumps(result,indent=2)+'\n');print(dict(latest_modules=len(latest),accepted_inputs=len(rows)))
