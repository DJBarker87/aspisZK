"""Read-only source/receipt preflight. This does not replay Lean or prove a ROW."""
from pathlib import Path
import json,hashlib,re,subprocess,sys,datetime
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cbmid-20261027';lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
t=json.loads((out/'TALLY.json').read_text());assert len(set(t['used_ids']))==len(t['used_ids'])
assert all(40600<=x<=40899 for x in t['used_ids']);assert set(t['lean_charged'])<=set(t['used_ids'])
assert len(t['lean_charged'])<=100 and len(t['kani_charged'])<=10
receipts={a:json.loads((out/f'{a}.json').read_text()) for a in t['lean_charged']}
for ordinal,a in enumerate(t['lean_charged'],1):
 r=receipts[a];assert r['attempt']==a
 if ordinal>=98:assert any(x in r['module'] for x in ['Audit','Manifest','Bundle'])
 if r['exit']==0:
  for line in r.get('axioms',[]):
   if 'depends on axioms:' in line:
    names=re.search(r'\[([^]]*)\]',line)[1].split(',')
    assert set(n.strip() for n in names)<={'propext','Classical.choice','Quot.sound'},(a,line)
current={};pending=[]
for p in sorted(lean.glob('PV_CBM_*.lean')):
 s=p.read_text();bad=re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^\s*axiom\s',s,re.M)
 assert not bad,(p,bad.group())
 sha=hashlib.sha256(s.encode()).hexdigest();name='R1Z/'+p.stem
 matches=[r for r in receipts.values() if r['module']==name and r['source_sha256']==sha and r['exit']==0]
 if matches:
  r=matches[-1];current[name]=dict(source=str(p.relative_to(root)),sha256=sha,receipt=r['attempt'],imports=re.findall(r'^import (\S+)',s,re.M))
 else:pending.append(name)
# Acyclicity for the current owned-module graph, with explicit pending imports.
visiting=set();visited=set()
def visit(name):
 assert name not in visiting,name
 if name in visited:return
 visiting.add(name)
 for dep in current[name]['imports']:
  n=dep.replace('.','/')
  if n in current:visit(n)
 visiting.remove(name);visited.add(name)
for name in current:visit(name)
for name in t['kani_charged']:
 p=out/name/'receipt.json'
 if not p.exists():continue # running is reported separately, never a pass
 r=json.loads(p.read_text());args=r['target']
 assert '--unwinding-assertions' in args and '--cpu-list' in args
 assert args[args.index('--cpu-list')+1]=='0-3'
 assert not any('stub' in a for a in args)
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),scope='static source/receipt audit only; not a Lean replay, source law, or release claim',lean_charged=len(t['lean_charged']),kani_charged=len(t['kani_charged']),rows_before=0,rows_after=t.get('rows_after',0),current=current,pending=pending,source_counterexample=False)
(out/'STATIC-AUDIT.json').write_text(json.dumps(r,indent=2)+'\n')
print('current',len(current),'pending',pending,'Lean',len(t['lean_charged']),'Kani',len(t['kani_charged']))
if '--require-current' in sys.argv:assert not pending,pending
