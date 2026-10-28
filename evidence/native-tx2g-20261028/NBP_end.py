from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
code='''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-native-tx2g-20261028');cache=Path('/home/dombarker/project-offloads/codex-cx-tx2low-cache-20261028')
scopes=[]
for p in sorted(b.glob('NBP_[KL]*/receipt.json')):
 r=json.loads(p.read_text());cg=Path(r['cgroup']);procs=(cg/'cgroup.procs').read_text().strip() if (cg/'cgroup.procs').exists() else ''
 scopes.append(dict(attempt=r['attempt'],cgroup=str(cg),populated=bool(procs)));assert not procs,(r['attempt'],procs)
start=json.loads((b/'NBP_CACHE_START.json').read_text())
end={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}
changed=[p for p,x in start.items() if end.get(p)!=dict(sha256=x['sha256'],bytes=x['bytes'])];assert not changed,changed
root=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
library={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in [root/'Aeneas.olean']+list((root/'Aeneas').rglob('*.olean'))}
assert library==json.loads((b/'NBP_LIBRARY_START.json').read_text()),'Aeneas drift'
cleaned=[]
for name in ['NBP_target','NBP_tmp','.lake']:
 p=b/name
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);cleaned.append(dict(path=str(p),bytes=size))
files={'NBP_CACHE_END.json':end,'NBP_LIBRARY_END.json':library,'NBP_END.json':dict(scopes=scopes,all_scopes_terminal=True,unchanged_start_cache=True,library_unchanged=True,persistent_cache=str(cache),persistent_cache_retained=cache.is_dir(),cleaned=cleaned)}
for n,x in files.items():(b/n).write_text(json.dumps(x,indent=2)+'\\n')
print(json.dumps(files))
'''
# This mutating cleanup is submitted once only. If transport fails afterward,
# recover the named end receipts read-only, never repeat the cleanup.
r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
(E/'NBP_END_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr))+'\n')
if r.returncode==255:
 for n in range(10):
  time.sleep(60)
  recover="from pathlib import Path;import json;b=Path('/home/dombarker/project-offloads/codex-cx-native-tx2g-20261028');names=['NBP_CACHE_END.json','NBP_LIBRARY_END.json','NBP_END.json'];print(json.dumps({n:json.loads((b/n).read_text()) for n in names if (b/n).is_file()}))"
  r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3'],input=recover,capture_output=True,text=True)
  (E/f'NBP_END-recovery-{n}.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255:break
assert r.returncode==0,r.stderr
files=json.loads(r.stdout);assert 'NBP_END.json' in files,'missing submitted cleanup receipt; do not repeat'
for n,x in files.items():(E/n).write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(files['NBP_END.json'],indent=2)[-1500:])
