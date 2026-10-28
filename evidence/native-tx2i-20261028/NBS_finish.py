"""Read-only final pins, source validation and owned rebuildable-target cleanup.
No prover, Rust arithmetic gate, shared infrastructure mutation, or cache deletion."""
from pathlib import Path
import json,hashlib,subprocess,base64,zlib,time
from NBS_expected import expected
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2i-20261028'
x=expected(E/'NBS_accessor.patch');m=x['after']
# Before/after are equal: every desired patch already has its terminal receipt.
assert x['apply'] is False
(E/'NBS_FINAL_SOURCE_MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
old=json.loads((E.parent/'native-tx2h-20261028/NBQ_SCRATCH_MANIFEST.json').read_text())
errors=[];inherited=[]
for name,pin in old.items():
 p=Path(name)
 if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==pin:continue
 if name.startswith(('crates/','programs/')):errors.append(name);continue
 head=subprocess.check_output(['git','show','HEAD:'+name]);assert p.read_bytes()==head,('own non-target mutation',name)
 inherited.append(dict(path=name,frozen_sha256=pin,inherited_head_sha256=hashlib.sha256(head).hexdigest()))
assert not errors,errors
(E/'NBS_REPOSITORY_SOURCE_CHECK.json').write_text(json.dumps(dict(frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',checked=len(old),shipped_files_unchanged=True,errors=errors,inherited_non_target_differences=inherited),indent=2)+'\n')
blob=base64.b64encode(zlib.compress(json.dumps(m).encode())).decode()
code=f'''from pathlib import Path
import hashlib,json,base64,zlib,shutil
b=Path({B!r});s=b/'NBS_src';expected=json.loads(zlib.decompress(base64.b64decode({blob!r})))
errors=[n for n,h in expected.items() if not (s/n).is_file() or hashlib.sha256((s/n).read_bytes()).hexdigest()!=h]
assert not errors,errors
cache=Path('/home/dombarker/project-offloads/codex-cx-tx2mid-cache-20261028')
cache_pins={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}}
a=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
libs={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in [a/'Aeneas.olean']+list((a/'Aeneas').rglob('*.olean'))}}
scopes=[]
for p in sorted(b.glob('NBS_[LK][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());cg=Path(r['cgroup']);events=(cg/'cgroup.events').read_text() if cg.exists() else 'removed'
 assert events=='removed' or 'populated 0' in events,(p,events)
 scopes.append(dict(attempt=r['attempt'],exit=r['exit_status'],cgroup=r['cgroup'],events=events))
removed=[]
for name in ['NBS_target','NBS_tmp']:
 p=b/name
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());removed.append(dict(path=str(p),bytes=size));shutil.rmtree(p)
print(json.dumps(dict(source=dict(checked=len(expected),errors=errors,lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest()),cache=cache_pins,library=libs,scopes=scopes,removed=removed,persistent_cache_retained=cache.is_dir())))
'''
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
 with (E/'NBS_END_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if trial<10:time.sleep(60)
 else:raise SystemExit('transport exhausted')
assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
assert out['source']['lock_sha256']==hashlib.sha256(subprocess.check_output(['git','show','4bb3b3f5:Cargo.lock'])).hexdigest()
for key,name in [('cache','NBS_CACHE_END.json'),('library','NBS_LIBRARY_END.json')]:
 (E/name).write_text(json.dumps(out.pop(key),indent=2)+'\n')
(E/'NBS_END.json').write_text(json.dumps(out,indent=2)+'\n')
start=json.loads((E/'NBS_CACHE_START.json').read_text());end=json.loads((E/'NBS_CACHE_END.json').read_text())
assert all(end.get(k)==v for k,v in start.items()),'initial cache objects changed'
assert json.loads((E/'NBS_LIBRARY_START.json').read_text())==json.loads((E/'NBS_LIBRARY_END.json').read_text()),'Aeneas pins changed'
print(json.dumps(dict(source=out['source'],scopes=len(out['scopes']),cache_start=len(start),cache_end=len(end),removed=out['removed'])))
