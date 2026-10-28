"""Read-only pin audit; remove only this job's disposable Rust/solver outputs."""
from pathlib import Path
import subprocess,json,hashlib,tarfile,io,time
from NCN_expected import expected
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-native-tx2r-20261028'
latest=expected(E/'NCN_query_generic.patch')['after']
raw=subprocess.check_output(['git','archive','4bb3b3f5','Cargo.toml','Cargo.lock','crates','programs','audit','xtask'])
with tarfile.open(fileobj=io.BytesIO(raw),mode='r:') as tar:
 frozen={p.name:hashlib.sha256(tar.extractfile(p).read()).hexdigest() for p in tar if p.isfile()}
payload=dict(expected={**frozen,**latest},initial=json.loads((E/'NCN_CACHE_START.json').read_text()),launchers=json.loads((E/'NCN_LAUNCHER_INPUTS.json').read_text()))
code='''from pathlib import Path
import json,hashlib,shutil
b=Path(%r);s=b/'NCI_src';x=json.loads(%r)
drift=[n for n,h in x['expected'].items() if not (s/n).is_file() or hashlib.sha256((s/n).read_bytes()).hexdigest()!=h]
assert not drift,('scratch drift',drift)
changed=[n for n,v in x['initial'].items() if not Path(n).is_file() or hashlib.sha256(Path(n).read_bytes()).hexdigest()!=v['sha256']]
assert not changed,('imported cache drift',changed)
assert all((b/n).read_text()==v for n,v in x['launchers'].items()),'unchanged launcher inputs drifted'
cache=Path('/home/dombarker/project-offloads/codex-cx-tx2resume-cache-20261028')
c=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
roots=[cache,c/'objects',c,c/'objects',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
rels=['Aeneas.olean','Aeneas.olean.private','Aeneas.olean.server','Aeneas.ir']
rels+=['Aeneas/'+str(p.relative_to(c/'objects'/'Aeneas')) for p in (c/'objects'/'Aeneas').rglob('*') if p.is_file()]
resolved={}
for rel in rels:
 q=next((root/rel for root in roots if (root/rel).is_file()),None)
 if q:resolved[rel]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size)
pins=json.loads((b/'NCN_LIBRARY_PIN.json').read_text())
assert all(resolved[str(Path(n).relative_to(c/'objects'))]['sha256']==v['sha256'] for n,v in pins.items()),'library pin drift'
status={}
for receipt in sorted(b.glob('NCN_[KL][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(receipt.read_text());procs=Path(r['cgroup'])/'cgroup.procs'
 status[r['attempt']]=procs.read_text().strip() if procs.exists() else 'scope removed'
assert all(v in ['', 'scope removed'] for v in status.values()),'owned scope still populated'
solver=b/'NCN_tmp';solver_files=list(solver.iterdir()) if solver.exists() else []
assert all(p.is_file() for p in solver_files),'inspect unexpected solver directory'
solver_bytes=sum(p.stat().st_size for p in solver_files)
for p in solver_files:p.unlink()
target=b/'NCN_target';assert not target.is_symlink()
size=sum(p.stat().st_size for p in target.rglob('*') if p.is_file()) if target.exists() else 0
if target.exists():shutil.rmtree(target)
result=dict(scratch_files_checked=len(x['expected']),scratch_drift=drift,imported_cache_files_checked=len(x['initial']),cache_drift=changed,own_cache_retained=str(cache),owned_scopes=status,owned_target_bytes_removed=size,solver_files_removed=len(solver_files),solver_bytes_removed=solver_bytes,library=resolved,launchers_unchanged=True)
(b/'NCN_END.json').write_text(json.dumps(result,indent=2)+'\\n');print(json.dumps(result))
'''%(B,json.dumps(payload))
# Source/pin recovery only; this script never launches a prover.
for retry in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3 -'],input=code,capture_output=True,text=True)
 (E/f'NCN_END-transport-{retry}.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stdout+r.stderr
result=json.loads(r.stdout);(E/'NCN_END.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'NCN_LIBRARY_START.json').write_bytes((E/'NCN_LIBRARY_PIN.json').read_bytes())
print(json.dumps({k:v for k,v in result.items() if k not in ['owned_scopes','library']}));print('Pinned Aeneas artifacts',len(result['library']))
