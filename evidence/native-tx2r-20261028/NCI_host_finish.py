"""Own read-only pin checks and cleanup of owned disposable Rust/solver outputs."""
from pathlib import Path
import subprocess,json,hashlib,tarfile,io,shlex,time
from NCI_expected import expected
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-tx2r-20261028'
latest=expected(E/'NCI_last.patch')['after']
raw=subprocess.check_output(['git','archive','4bb3b3f5','Cargo.toml','Cargo.lock','crates','programs','audit','xtask'])
with tarfile.open(fileobj=io.BytesIO(raw),mode='r:') as tar:
 frozen={p.name:hashlib.sha256(tar.extractfile(p).read()).hexdigest() for p in tar if p.isfile()}
expected_sources={**frozen,**latest}
p=json.loads((E/'NCI_TX1_PREFLIGHT.json').read_text());names=[x['module'] for x in p['missing']]+p['unknown']
code='''from pathlib import Path
import json,hashlib,shutil
b=Path(%r);s=b/'NCI_src'
expected=json.loads(%r)
drift=[n for n,h in expected.items() if not (s/n).is_file() or hashlib.sha256((s/n).read_bytes()).hexdigest()!=h]
assert not drift,('owned scratch source drift',drift)
cache=Path('/home/dombarker/project-offloads/codex-cx-tx2resume-cache-20261028')
initial=json.loads((b/'NCI_CACHE_START.json').read_text())
changed=[n for n,v in initial.items() if not Path(n).is_file() or hashlib.sha256(Path(n).read_bytes()).hexdigest()!=v['sha256']]
assert not changed,('imported cache drift',changed)
c=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
roots=[cache,c/'objects',c,c/'objects',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
rels=['Aeneas.olean','Aeneas.olean.private','Aeneas.olean.server','Aeneas.ir']
rels+=['Aeneas/'+str(p.relative_to(c/'objects'/'Aeneas')) for p in (c/'objects'/'Aeneas').rglob('*') if p.is_file()]
resolved={}
for rel in rels:
 q=next((root/rel for root in roots if (root/rel).is_file()),None)
 if q:resolved[rel]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size)
pins=json.loads((b/'NCI_LIBRARY_PIN.json').read_text())
assert all(resolved[str(Path(n).relative_to(c/'objects'))]['sha256']==v['sha256'] for n,v in pins.items())
names=json.loads(%r)
available={};missing=[]
for n in names:
 rel=n.replace('.','/')+'.olean';q=next((root/rel for root in roots if (root/rel).is_file()),None)
 if q:available[n]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest())
 else:missing.append(n)
status={}
for receipt in sorted(b.glob('NCI_[KL][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(receipt.read_text());cg=Path(r['cgroup']);procs=cg/'cgroup.procs';status[r['attempt']]=procs.read_text().strip() if procs.exists() else 'scope removed'
assert all(x in ['', 'scope removed'] for x in status.values()),'an owned scope is still populated'
solver=list((b/'NCI_tmp').glob('*'));assert not solver,'inspect owned solver files before cleanup'
target=b/'NCI_target';size=sum(x.stat().st_size for x in target.rglob('*') if x.is_file()) if target.exists() else 0
if target.exists():shutil.rmtree(target)
result=dict(scratch_files_checked=len(expected),scratch_drift=drift,imported_cache_files_checked=len(initial),cache_drift=changed,own_cache_retained=str(cache),owned_scopes=status,owned_target_bytes_removed=size,solver_files_remaining=0,library=resolved,tx1=dict(scope='actual file-availability check in the specified LEAN_PATH only; no dependency compile',requested=len(names),available=available,missing=missing,missing_count=len(missing)))
(b/'NCI_END.json').write_text(json.dumps(result,indent=2)+'\\n')
print(json.dumps(result))
'''%(B,json.dumps(expected_sources),json.dumps(names))
# Post-proof metadata recovery only; no prover can be resubmitted here.
for retry in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3 -'],input=code,capture_output=True,text=True)
 (E/f'NCI_END-transport-{retry}.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stdout+r.stderr
result=json.loads(r.stdout);(E/'NCI_END.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['owned_scopes','library','tx1']}));print('TX1 missing objects',result['tx1']['missing_count'])
