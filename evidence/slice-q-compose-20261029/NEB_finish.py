"""Read-only source/cache postflight, then preserve own accepted objects and clean own rebuildable scratch."""
from pathlib import Path
import json,subprocess,hashlib,shlex,time
E=Path(__file__).resolve().parent;R=E.parent.parent;B='/home/dombarker/project-offloads/codex-cx-slice-q-compose-20261029';CACHE='/home/dombarker/project-offloads/codex-cx-slice-q-compose-cache-20261029'
assert not (E/'NEB_ACTIVE.json').exists()
receipts=[json.loads(p.read_text()) for p in E.glob('NEB_[LKE]*/receipt.json')];mods=[]
for d in receipts:
 if d['kind']=='lean' and d['exit_status']==0 and d['module'] not in mods:
  m=d['module'];f=E/(m.replace('.','/')+'.lean')
  if not f.exists() or hashlib.sha256(f.read_bytes()).hexdigest()==d['source_hashes'].get(m.replace('.','/')+'.lean'):mods.append(m)
payload=dict(cache=json.loads((E/'NEB_CACHE_IMPORTS.json').read_text()),peer=json.loads((E/'NEB_SIBLING_OBJECT_IMPORTS.json').read_text()),library=json.loads((E/'NEB_SOURCE.json').read_text())['library'],modules=mods,cgroups=[d['cgroup'] for d in receipts])
code='''from pathlib import Path
import hashlib,json,sys,shutil
b=Path('''+repr(B)+''');cache=Path('''+repr(CACHE)+''');d=json.load(sys.stdin);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();errors=[]
for group in ['cache','peer']:
 for f in d[group]:
  p=Path(f['destination'])
  if not p.is_file() or sha(p)!=f['sha256']:errors.append(str(p))
for p,h in d['library'].items():
 if sha(Path(p))!=h:errors.append(p)
pins=json.loads((b/'NEB_SOURCE_PINS.json').read_text())
for n,h in pins.items():
 if sha(b/'NEB_src'/n)!=h:errors.append('scratch:'+n)
for p,v in json.loads((b/'NEB_TOOL_PINS.json').read_text()).items():
 if sha(Path(p))!=v['sha256']:errors.append('tool:'+p)
for group in d['cgroups']:
 p=Path('/sys/fs/cgroup')/group.lstrip('/')/'pids.current'
 if p.is_file() and int(p.read_text())!=0:errors.append('live scope:'+group)
assert not errors,errors
export=cache/'NEB_exports_20261029';export.mkdir(exist_ok=True);objects=[]
for m in d['modules']:
 key=m.replace('.','/')+'.olean'
 for p in b.glob(key+'*'):
  q=export/p.relative_to(b);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert sha(q)==sha(p)
  else:shutil.copy2(p,q)
  objects.append(dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size))
assert objects
# Only this lane's exact allowlisted rebuildable target/temp directories.
removed=[]
for name in ['NEB_target','NEB_ref_target','NEB_additive_ref_target','NEB_representation_ref_target','NEB_tmp']:
 p=b/name;assert p.parent==b and not p.is_symlink()
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file() and not q.is_symlink());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
# Remove owned compiled object scratch after preserving accepted objects.
# The persistent cache, all source snapshots and receipts are retained.
removed_objects=0
for p in list(b.rglob('*.olean*')):
 if p.is_file() and not p.is_symlink():p.unlink();removed_objects+=1
print(json.dumps(dict(cache_seed_files=len(d['cache']),peer_objects=len(d['peer']),library_objects=len(d['library']),native_source_files=len(pins),source_cache_library_tool_errors=[],all_owned_scopes_terminal=True,lock_sha256=sha(b/'NEB_src/Cargo.lock'),object_exports=objects,export_directory=str(export),removed_rebuildable=removed,removed_owned_object_scratch=removed_objects,persistent_cache_retained=str(cache),keys_or_wallets_touched=False)))
'''
for retry in range(11):
 p=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True)
 if p.returncode!=255:break
 # A postflight mutation may already have executed: recover read-only, never
 # resubmit cleanup/export. Preserve the uncertainty and stop for recovery.
 (E/'NEB_FINISH_TRANSPORT_ERROR.json').write_text(json.dumps(dict(exit=255,stderr=p.stderr,recovery='Read-only recovery required; do not resubmit mutations'),indent=1));raise SystemExit('postflight transport: recover read-only')
assert p.returncode==0,p.stdout+p.stderr
d=json.loads(p.stdout);d.update(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,lean_attempts=len(list(E.glob('NEB_L*/receipt.json'))),kani_attempts=len(list(E.glob('NEB_K*/receipt.json'))),extraction_attempts=len(list(E.glob('NEB_E*/receipt.json'))),new_module_axioms_audit='NEB_L079/receipt.json',local_frozen_crates_programs_unchanged=not subprocess.check_output(['git','diff','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs'],cwd=R),caches_never_deleted=True)
(E/'NEB_END.json').write_text(json.dumps(d,indent=1)+'\n');print(json.dumps({k:d[k] for k in ['cache_seed_files','peer_objects','library_objects','native_source_files','all_owned_scopes_terminal','removed_owned_object_scratch','lean_attempts','kani_attempts']}))
