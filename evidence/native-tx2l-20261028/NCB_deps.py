"""Select missing unchanged imports only; compile serially with unchanged backend."""
from pathlib import Path
import subprocess,json,re,sys
E=Path(__file__).resolve().parent
roots=['/home/dombarker/project-offloads/codex-cx-tx2mid-cache-20261028','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean']
code='from pathlib import Path; import json; print(json.dumps(sorted(set(str(p.relative_to(Path(r)))[:-6].replace("/", ".") for r in '+repr(roots)+' for p in Path(r).rglob("*.olean")))))'
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+__import__('shlex').quote(code)],capture_output=True,text=True)
assert r.returncode==0,r.stderr
# Exact original sources selected by the replayed headline predecessor; no
# namespace/source reconstruction from renamed replay files.
replay=json.loads(Path('evidence/replay-dry8-20261026/RPz7_plan.json').read_text())
verification=json.loads(Path('evidence/replay-dry8-20261026/RPz7_final-verification.json').read_text())
authority={r['original']:(r['original_source'],r['original_sha256']) for r in replay['rows']}
for row in verification['selected_reused_source_checks']:
 if row.get('selected_source') and row.get('expected_sha256'):
  authority[row['module']]=(row['selected_source'],row['expected_sha256'])
have=set(json.loads(r.stdout));plan=[];seen=set()
def visit(m):
 if m in have or m in seen:return
 seen.add(m)
 p=next((p for base in ['lean','docs/research/100bit-spend-path-20261013/lean'] if (p:=Path(base)/Path(m.replace('.','/')+'.lean')).is_file()),None)
 if p is None and m in authority:
  name,pin=authority[m];p=Path(name)
  assert p.is_file(),('pinned source absent',m,name)
  actual=__import__('hashlib').sha256(p.read_bytes()).hexdigest()
  assert actual==pin,('pinned source drift',m,actual,pin)
  selection=E/'NCB_DEP_SOURCE_SELECTION.json'
  records=json.loads(selection.read_text()) if selection.exists() else {}
  records[m]=dict(source=name,sha256=actual,authority='RPz7 original planning/reused source selection; replay-dry9 selected-source check')
  selection.write_text(json.dumps(records,indent=2)+'\n')
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
(E/'NCB_DEP_PLAN.json').write_text(json.dumps(plan,indent=2))
if __import__('os').environ.get('NCB_PLAN_ONLY'):
 print(json.dumps(plan));raise SystemExit
for m,p in plan:
 n=1+len(list(E.glob('NCB_L[0-9][0-9][0-9].json')));assert n<=80
 a=f'NCB_L{n:03}'
 r=subprocess.run([sys.executable,str(E/'NCB_build.py'),a,p,m],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 receipt=E/a/'receipt.json'
 if not receipt.exists():print(r.stdout+r.stderr,flush=True);raise SystemExit('STOP no receipt')
 x=json.loads(receipt.read_text());print(m,a,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status'] or r.returncode: print(r.stdout+r.stderr,flush=True);raise SystemExit('STOP failed target')
