"""Select missing unchanged imports only; compile serially with unchanged backend."""
from pathlib import Path
import subprocess,json,re,sys
E=Path(__file__).resolve().parent
roots=['/home/dombarker/project-offloads/codex-cx-tx2mid-cache-20261028','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean']
code='from pathlib import Path; import json; print(json.dumps(sorted(set(str(p.relative_to(Path(r)))[:-6].replace("/", ".") for r in '+repr(roots)+' for p in Path(r).rglob("*.olean")))))'
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+__import__('shlex').quote(code)],capture_output=True,text=True)
assert r.returncode==0,r.stderr
have=set(json.loads(r.stdout));plan=[];seen=set()
def visit(m):
 if m in have or m in seen:return
 seen.add(m)
 p=next((p for base in ['lean','docs/research/100bit-spend-path-20261013/lean'] if (p:=Path(base)/Path(m.replace('.','/')+'.lean')).is_file()),None)
 if p is None:
  candidates=list(Path('docs/research/100bit-spend-path-20261013/lean').rglob(m.replace('.','/')+'.lean'))
  if not candidates:
   candidates=list(Path('docs/research/100bit-spend-path-20261013/lean-candidates').rglob(m.split('.')[-1]+'.lean'))
  if not candidates and m in have:return
  assert candidates,('missing source',m)
  hashes={__import__('hashlib').sha256(q.read_bytes()).hexdigest() for q in candidates}
  if len(hashes)!=1 and m in have:return # Preserve the selected cached object; never guess an alternate source.
  assert len(hashes)==1,('ambiguous source',m,[str(q) for q in candidates])
  p=candidates[0]
 assert p is not None,('missing source',m)
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():visit(dep)
 if m not in have:plan.append((m,str(p)))
for m in sys.argv[1:]:visit(m)
(E/'NBS_DEP_PLAN.json').write_text(json.dumps(plan,indent=2))
if __import__('os').environ.get('NBS_PLAN_ONLY'):
 print(json.dumps(plan));raise SystemExit
for m,p in plan:
 n=1+len(list(E.glob('NBS_L[0-9][0-9][0-9].json')));assert n<=100
 a=f'NBS_L{n:03}'
 r=subprocess.run([sys.executable,str(E/'NBS_build.py'),a,p,m],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 receipt=E/a/'receipt.json'
 if not receipt.exists():print(r.stdout+r.stderr,flush=True);raise SystemExit('STOP no receipt')
 x=json.loads(receipt.read_text());print(m,a,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status'] or r.returncode: print(r.stdout+r.stderr,flush=True);raise SystemExit('STOP failed target')
