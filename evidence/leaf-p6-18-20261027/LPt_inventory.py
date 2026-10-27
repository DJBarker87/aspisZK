from pathlib import Path
import json,hashlib,subprocess,shlex,time
E=Path(__file__).resolve().parent
host='dombarker@100.108.41.90'
code='''from pathlib import Path
import hashlib,json
cache=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027')
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
roots=[cache,Path('/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027/XRw_objects'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
names=set()
for r in roots:
 for p in ([r/'Aeneas.olean']+list((r/'Aeneas').rglob('*.olean'))):
  if p.is_file():names.add(str(p.relative_to(r)))
selected={n:next(r/n for r in roots if (r/n).is_file()) for n in names}
print(json.dumps(dict(cache={str(p):pin(p) for p in cache.rglob('*') if p.is_file()},aeneas={str(p):pin(p) for p in selected.values()})))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',host,'python3 -c '+shlex.quote(code)],capture_output=True,text=True)
 with (E/'LPt_FINAL_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode==0:break
 if r.returncode!=255 or retry==10:raise SystemExit(r.stderr)
 time.sleep(60)
remote=json.loads(r.stdout)
(E/'LPt_CACHE_START.json').write_text(json.dumps(remote['cache'],indent=2)+'\n')
(E/'LPt_LIBRARY_START.json').write_text(json.dumps(remote['aeneas'],indent=2)+'\n')
