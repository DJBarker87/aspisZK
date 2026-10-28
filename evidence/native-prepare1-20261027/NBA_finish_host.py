"""Final read-only tool pin and bounded own scratch cleanup; no builds."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
def remote(code,label,submitted=False):
 for n in range(11):
  r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
  with (E/'NBA_FINISH_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(label=label,trial=n,exit=r.returncode,stderr=r.stderr,submitted=submitted))+'\n')
  if r.returncode!=255 or submitted:return r
  if n<10:time.sleep(60)
 raise RuntimeError('transport exhausted')
code='''from pathlib import Path
import json,hashlib,datetime
home=Path('/home/dombarker')
def pin(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while data:=f.read(1048576):h.update(data)
 return dict(path=str(p),resolved=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
paths=[home/'.cargo/bin/cargo-kani',home/'.cargo/bin/kani',home/'.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean']
for d in (home/'.kani').glob('kani-*'):
 for n in ['kani-compiler','cbmc','goto-instrument','kissat','cargo-kani']:
  if (d/'bin'/n).is_file():paths.append(d/'bin'/n)
p=home/'.cargo/.crates2.json';installed=[]
if p.is_file():
 x=json.loads(p.read_text()).get('installs',{})
 installed=[k for k,v in x.items() if 'cargo-kani' in v.get('bins',[])]
print(json.dumps(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),tools=[pin(p) for p in paths if p.is_file()],installed_kani=installed,qualification='Final fresh binary hashes. No fresh initial Rust binary hash claimed; inherited CLOSED leaf pins and exact command/version provenance remain retained.')))
'''
r=remote(code,'tools');assert r.returncode==0,r.stderr
(E/'NBA_TOOLCHAIN_END.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
# Only these three generated paths may be removed. Persistent leaf cache and
# source corpus are outside this allowlist and are never traversed or deleted.
code='''from pathlib import Path
import json,shutil,datetime
b=Path('/home/dombarker/project-offloads/codex-cx-native-prepare1-20261027')
removed=[]
for n in ['NBA_target','NBA_tmp','.lake']:
 p=b/n
 if not p.exists():continue
 assert p.resolve().is_relative_to(b.resolve()),str(p)
 assert not p.is_symlink(),str(p)
 shutil.rmtree(p);removed.append(str(p))
cache=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027')
assert cache.is_dir()
print(json.dumps(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),removed=removed,persistent_cache_retained=str(cache),scratch_sources_retained=str(b/'NBA_src'),keys_created=False,keys_deleted=False)))
'''
r=remote(code,'cleanup',submitted=True)
(E/'NBA_CLEANUP_LAUNCH.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,'Do not repeat cleanup blindly; inspect read-only: '+r.stderr
(E/'NBA_CLEANUP.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print(json.dumps(json.loads(r.stdout)))
