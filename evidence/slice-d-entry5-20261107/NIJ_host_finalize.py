"""I/O retention only; no compiler, prover, arithmetic gate, or cache deletion."""
from pathlib import Path
import hashlib,json,shutil,time,os
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry5-20261107');C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104');start=time.monotonic()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
# Never retain failed/stale objects as reusable certificates.
accepted={};excluded=[]
for config in sorted(B.glob('NIJ_L[0-9][0-9][0-9].json')):
 x=json.loads(config.read_text());receipt=B/x['attempt']/'receipt.json'
 if x['kind']!='lean' or not receipt.exists():continue
 rc=json.loads(receipt.read_text());module=x['module'];source=B/'NIJ_generated'/(module.replace('.','/')+'.lean')
 if rc['exit_status']==0 and source.is_file() and sha(source) in rc['source_hashes'].values():accepted[module]=x['attempt']
for p in sorted((B/'NIJ_objects').rglob('*')):
 if not p.is_file():continue
 rel=str(p.relative_to(B/'NIJ_objects'));module=rel.split('.')[0].replace('/','.')
 if module not in accepted:excluded.append(rel);continue
 assert rel.split('/')[0].startswith('NIJ_')
 rows.append(dict(path=rel,sha256=sha(p),bytes=p.stat().st_size))
tree=hashlib.sha256(json.dumps(rows,sort_keys=True).encode()).hexdigest();dest=C/('NIJ_exports_20261107_'+tree[:12]);dest.mkdir(parents=True,exist_ok=True)
for row in rows:
 src=B/'NIJ_objects'/row['path'];p=dest/row['path'];p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert sha(p)==row['sha256']
 else:shutil.copy2(src,p)
 assert sha(p)==row['sha256']
# Validate every resolved read-only dependency, including the exact Aeneas objects.
pins={};conflicts=[]
for p in sorted(B.glob('NIJ_L[0-9][0-9][0-9].json')):
 x=json.loads(p.read_text())
 for key,d in x.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  q=Path(d['path']);h=d['sha256']
  if str(q).startswith(str(B)+'/'):continue
  if str(q) in pins and pins[str(q)]!=h:conflicts.append(str(q))
  pins[str(q)]=h
changed=[dict(path=p,expected=h,actual=sha(Path(p)) if Path(p).is_file() else None) for p,h in pins.items() if not Path(p).is_file() or sha(Path(p))!=h]
assert not conflicts and not changed,(conflicts,changed)
# Remove only known own Rust/solver outputs after retaining objects. If any
# potential wallet key is present, retain the entire directory by default.
cleanup=[]
for name in ['NIJ_target','NIJ_tmp','NHR_target']:
 root=B/name
 if not root.exists():continue
 assert root.parent==B and not root.is_symlink()
 keys=[];bytes_=0;files=0
 for p in root.rglob('*'):
  if not p.is_file():continue
  files+=1;bytes_+=p.stat().st_size
  if p.suffix in ['.pem','.key'] or p.name.endswith('-keypair.json'):keys.append(str(p));continue
  if p.suffix=='.json' and p.stat().st_size<=4096:
   try:x=json.loads(p.read_text())
   except (ValueError,UnicodeError):continue
   if isinstance(x,list) and len(x) in [32,64] and all(type(v) is int and 0<=v<=255 for v in x):keys.append(str(p))
 if keys:cleanup.append(dict(path=str(root),retained=True,reason='potential key; default retention',files=files,bytes=bytes_,potential_keys=keys))
 else:shutil.rmtree(root);cleanup.append(dict(path=str(root),retained=False,reason='owned compiler/solver outputs only, no potential key found',files=files,bytes=bytes_))
export=dict(directory=str(dest),tree_sha256=tree,files=rows,total_bytes=sum(r['bytes'] for r in rows),never_deleted_cache=True,accepted_green_modules=accepted,excluded_failed_or_stale_objects=excluded,read_only_dependencies_verified=len(pins),read_only_dependencies_unchanged=True)
(B/'NIJ_CACHE_EXPORT.json').write_text(json.dumps(export,indent=1)+'\n')
stat=shutil.disk_usage(B)
(B/'NIJ_HOST_FINAL.json').write_text(json.dumps(dict(action='I/O retention/checks and own output cleanup only',exit_status=0,wall_seconds=time.monotonic()-start,export=export,cleanup=cleanup,disk=dict(total=stat.total,used=stat.used,free=stat.free),wallet_keys_created=False,keys_deleted=False,refund_destination=None,refund_signatures=[],shared_workspaces_modified=False,cache_deleted=False),indent=1)+'\n')
print(json.dumps(dict(status='PASS_IO_RETENTION',export_bytes=export['total_bytes'],export_files=len(rows),read_only_dependencies=len(pins),cleanup=cleanup,disk_free=stat.free)))
