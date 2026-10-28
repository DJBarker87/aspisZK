from pathlib import Path
import subprocess,json,sys,time
E=Path(__file__).resolve().parent
assert not (E/'NCD_BATCH_ACTIVE').exists() and not (E/'NCD_NATIVE_BATCH_ACTIVE').exists()
code='''from pathlib import Path
import json,hashlib,os,shutil,re
b=Path('/home/dombarker/project-offloads/codex-cx-native-tx2m-20261028');c=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025');cache=Path('/home/dombarker/project-offloads/codex-cx-tx2mid-cache-20261028')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((b/'NCD_native_z1_plan.json').read_text());s=Path(p['scratch'])
drift=[n for n,h in p['source_manifest'].items() if not (s/n).is_file() or sha(s/n)!=h]
assert not drift,('source drift',drift)
start=json.loads((b/'NCD_LIBRARY_PIN.json').read_text());libdrift=[n for n,h in start.items() if sha(Path(n))!=h['sha256']];assert not libdrift,libdrift
sidecars={str(q):dict(sha256=sha(q),bytes=q.stat().st_size) for q in (c/'objects').rglob('Aeneas*') if q.is_file()}
for d in [(c/'objects'/'Aeneas')]:
 for q in d.rglob('*'):
  if q.is_file() and q.suffix in ['.olean','.private','.server','.ir']:sidecars[str(q)]=dict(sha256=sha(q),bytes=q.stat().st_size)
scopes=[]
for q in b.glob('NCD_[LK]*/receipt.json'):
 r=json.loads(q.read_text());cg=Path(r['cgroup'])/'cgroup.procs';procs=cg.read_text().strip() if cg.exists() else '';scopes.append(dict(attempt=r['attempt'],cgroup=r['cgroup'],processes=procs));assert not procs,('live own scope',r['attempt'],procs)
active=[]
for q in Path('/proc').iterdir():
 if not q.name.isdigit():continue
 try:
  cmd=(q/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace');cwd=(q/'cwd').resolve()
  if cmd and (cwd==b or str(b/'NCD_target') in cmd):active.append(dict(pid=q.name,command=cmd,cwd=str(cwd)))
 except (OSError,RuntimeError):pass
assert not active,('live own processes',active)
target=b/'NCD_target';size=sum(q.stat().st_size for q in target.rglob('*') if q.is_file()) if target.exists() else 0
assert target.parent==b and not target.is_symlink()
if target.exists():shutil.rmtree(target)
cleanup=[]
for q in (b/'NCD_tmp').rglob('*'):
 if q.is_file() and (q.name.startswith('external-sat') or q.name.startswith('smt2_dec_problem')):cleanup.append(dict(path=str(q),bytes=q.stat().st_size));q.unlink()
assert cache.is_dir();assert not drift and not libdrift
print(json.dumps(dict(source_files=len(p['source_manifest']),source_drift=drift,lock_sha256=sha(s/'Cargo.lock'),aeneas_base_pins_unchanged=True,aeneas_end_objects=sidecars,scopes=scopes,active=active,removed_target_bytes=size,removed_solver_files=cleanup,persistent_cache_retained=str(cache),own_objects={q.name:dict(sha256=sha(q),bytes=q.stat().st_size) for q in cache.glob('NCD_*.olean')})))
'''
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 with (E/'NCD_END_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))+'\n')
 if r.returncode==0:break
 if r.returncode!=255 or trial==10:raise SystemExit('STOP end validation '+r.stdout+r.stderr)
 time.sleep(60)
(E/'NCD_END.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n');print('end validation complete')
