from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
manifest=json.loads((E/'NFA_FINAL_MANIFEST.json').read_text())
code='''from pathlib import Path
import json,hashlib,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul4-20261029');C=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul4-cache-20261029/NFA_exports_20261104')
C.mkdir(exist_ok=True)
entries=[]
manifest=json.loads(MANIFEST)
for e in manifest['entries']:
 name=e['module'];source=B/'NFA_generated'/(name+'.lean')
 assert hashlib.sha256(source.read_bytes()).hexdigest()==e['source_sha256']
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NFA_objects'/(name+suffix)
  if not p.is_file():continue
  q=C/p.name;shutil.copyfile(p,q);h=hashlib.sha256(q.read_bytes()).hexdigest()
  assert h==hashlib.sha256(p.read_bytes()).hexdigest()
  entries.append(dict(module=name,source_attempt=e['source_attempt'],source_sha256=e['source_sha256'],source_path=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
# Post-timeout lock recovery. Every subsequent own launch first asserted the
# previous Cargo.lock text equals frozen before writing any payload file.
lock=B/'NFA_src/Cargo.lock';h=hashlib.sha256(lock.read_bytes()).hexdigest()
assert h=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
lockcheck=dict(attempt='NFA_K018',status='LATE_READ_ONLY_RECOVERY',current_sha256=h,subsequent_pre_upload_text_equality_assertion='NFA_K019: NFA_run.py verifies existing Cargo.lock==frozen text before all mutations',subsequent_run_lock_checks=['NFA_K019','NFA_K020','NFA_K021','NFA_K022'],unchanged=True)
# No live process may survive in any own attempted formal scope.
cgroups=[]
for rc in B.glob('NFA_*/receipt.json'):
 x=json.loads(rc.read_text());p=Path(x['cgroup']);procs=(p/'cgroup.procs').read_text().split() if (p/'cgroup.procs').exists() else []
 assert not procs,(x['attempt'],procs)
 cgroups.append(dict(attempt=x['attempt'],cgroup=str(p),pids=procs))
print(json.dumps(dict(exports=entries,cache=str(C),lock_recovery=lockcheck,terminal_cgroups=cgroups)))
'''
code=code.replace('MANIFEST',repr(json.dumps(manifest)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NFA_EXPORT_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'NFA_OBJECT_EXPORTS.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'NFA_K018-lock-recovery.json').write_text(json.dumps(out['lock_recovery'],indent=2)+'\n')
print(len(out['exports']),'exported objects/sidecars;',len(out['terminal_cgroups']),'terminal scopes')
