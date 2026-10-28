"""Read-only object pin recovery; then authorized own rebuildable scratch cleanup.
Persistent cache and source/evidence are NEVER removed."""
from pathlib import Path
import subprocess,json,time,shlex
E=Path(__file__).resolve().parent
assert not (E/'NBL_ACTIVE.json').exists(),'scope still active'
assert (E/'NBL_BUDGET_STOP.json').exists()
start=json.loads((E/'NBL_START.json').read_text())
code="""from pathlib import Path
import hashlib,json,datetime
x=START
cache=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027')
roots=[cache,Path('/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027/XRw_objects'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
end={str(p):pin(p) for p in cache.rglob('*') if p.is_file()}
changed=[n for n,v in x['cache'].items() if n not in end or v['sha256']!=end[n]['sha256']]
aeneas={}
for n,v in x['aeneas'].items():
 choices=[r/n for r in roots if (r/n).is_file()]
 assert choices,('unresolved Aeneas',n)
 p=choices[0];aeneas[n]=dict(path=str(p),**pin(p))
bad=[n for n,v in x['aeneas'].items() if v['sha256']!=aeneas[n]['sha256']]
print(json.dumps(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),cache=end,
 initial_cache_changes=changed,new_cache_files=[n for n in end if n not in x['cache']],
 resolved_aeneas=aeneas,aeneas_changes=bad)))
""".replace('START',repr(start))
def run(code):
 for n in range(11):
  r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
  with (E/'NBL_FINISH_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=n,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255:break
  if n<10:time.sleep(60)
 assert r.returncode==0,r.stderr
 return json.loads(r.stdout)
end=run(code);(E/'NBL_END.json').write_text(json.dumps(end,indent=2)+'\n')
assert not end['initial_cache_changes'],end['initial_cache_changes']
assert not end['aeneas_changes'],end['aeneas_changes']
# Only fixed own rebuildable directories. No key/source/persistent-cache cleanup.
cleanup="""from pathlib import Path
import shutil,json
base=Path('/home/dombarker/project-offloads/codex-cx-native-prepare2-20261027')
removed=[]
for name in ['NBL_target','NBL_tmp']:
 p=base/name
 if p.exists():
  assert p.is_dir() and not p.is_symlink()
  shutil.rmtree(p);removed.append(str(p))
assert Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027').is_dir()
print(json.dumps(dict(removed=removed,persistent_cache_retained=True,keys_created_or_deleted=False)))
"""
clean=run(cleanup);(E/'NBL_CLEANUP.json').write_text(json.dumps(clean,indent=2)+'\n')
print(json.dumps(dict(initial_cache_files=len(start['cache']),end_cache_files=len(end['cache']),
 initial_cache_changes=len(end['initial_cache_changes']),resolved_aeneas=len(end['resolved_aeneas']),
 aeneas_changes=len(end['aeneas_changes']),cleanup=clean)))
