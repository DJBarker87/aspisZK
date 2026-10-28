from NBW_host import *
import hashlib,fcntl
lock=(E/'NBW_SERIAL.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
r=py(f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028')
initial=json.loads((b/'NBW_CACHE_START.json').read_text())
changed=[]
for name,pin in initial.items():
 p=Path(name)
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=pin['sha256']:changed.append(name)
assert not changed,changed
lib=json.loads((b/'NBW_LIBRARY_PIN.json').read_text());resolution={{}}
roots=[cache,Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')]
for name,pin in lib.items():
 p=Path(name);rel=p.relative_to(roots[-1]);actual=next(q/rel for q in roots if (q/rel).is_file())
 assert hashlib.sha256(actual.read_bytes()).hexdigest()==pin['sha256'],str(actual)
 resolution[str(rel)]=dict(path=str(actual),sha256=pin['sha256'])
objects={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('NBW*') if p.is_file()}}
removed=[]
for p in (b/'NBW_tmp').rglob('*'):
 if p.is_file() and ((p.name.startswith('external-sat') and p.suffix=='.cnf') or p.name.startswith('smt2_dec_problem')):
  removed.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
target=b/'NBW_target';target_bytes=0
assert not target.is_symlink()
if target.exists():
 target_bytes=sum(p.stat().st_size for p in target.rglob('*') if p.is_file());shutil.rmtree(target)
print(json.dumps(dict(imported_cache_objects=len(initial),changed_imports=changed,aeneas_resolution=resolution,new_objects=objects,solver_removed=removed,target_removed_bytes=target_bytes,cache_retained=str(cache),scratch_retained=str(b/'NBW_src'),no_key_actions=True)))
''')
assert r.returncode==0,r.stderr
(E/'NBW_FINAL_HOST.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
rows=[]
for p in sorted(E.glob('NBW_*/receipt.json')):rows.append(json.loads(p.read_text()))
(E/'NBW_ATTEMPTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
summary={}
for kind in ['lean','kani','metadata']:
 xs=[x for x in rows if x.get('kind')==kind]
 summary[kind]=dict(attempts=len(xs),exits={str(rc):sum(x['exit_status']==rc for x in xs) for rc in sorted(set(x['exit_status'] for x in xs))})
summary['maximum_rss_kib']=max(int(x['peak_rss_kib']) for x in rows)
summary['all_swaps_zero']=all(int(x['swaps'])==0 for x in rows)
summary['copy_patch_sha256']=hashlib.sha256(Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest()
(E/'NBW_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))
