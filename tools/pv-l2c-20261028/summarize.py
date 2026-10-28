"""Derive budget and current-source status from raw receipts; never infer closure."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028';rows=[]
for p in sorted(E.glob('receipt-*.json')):
 x=json.loads(p.read_text());x['module']=x.get('module',x.get('target','').replace('/','.'));rows.append({k:x.get(k) for k in ['attempt','module','exit','accepted','source_revision','source_sha256','wall_seconds','peak_rss_bytes','swaps','axioms']})
used=sorted(int(p.stem.split('-')[1]) for p in E.glob('used-*.json'))
assert all(42600<=x<=42699 for x in used) and len(set(used))==len(used)
assert len(rows)<=100
compiled={x['attempt'] for x in rows};retired=[x for x in used if x not in compiled]
current=[]
for p in sorted((R/'docs/research/v8-r0-zk-20261009/lean').glob('PV_L2C_*.lean')):
 h=hashlib.sha256(p.read_bytes()).hexdigest();same=[x for x in rows if x['module']==p.stem and x['source_sha256']==h]
 accepted=[x for x in same if x['accepted']]
 current.append(dict(module=p.stem,path=str(p.relative_to(R)),sha256=h,accepted_attempts=[x['attempt'] for x in accepted],status='accepted current source' if accepted else 'not yet accepted'))
allowed={'propext','Classical.choice','Quot.sound'}
for x in rows:
 if not x['accepted']:continue
 for text in x['axioms']:
  if 'depends on axioms:' in text:
   names=set(re.findall(r'\[([^]]*)\]',text)[0].replace('\n','').split(','));names={s.strip() for s in names}
   assert names<=allowed,(x['attempt'],names)
kanis=[]
for p in sorted(E.glob('kani-*/receipt.json')):
 x=json.loads(p.read_text());kanis.append(dict(directory=p.parent.name,target=x['target'],exit=x['exit'],wall_seconds=x['wall_seconds'],credit='suspended: reached copy builtin, K-1' if p.parent.name=='kani-6' else 'no successful verification',source_revision=x['source_revision']))
assert len(kanis)<=6
out=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),base='e461dca06a993d32f4ebca368003e46add1ea884',lean_budget=100,lean_compile_attempts=len(rows),lean_accepted=sum(bool(x['accepted']) for x in rows),lean_failed=sum(not x['accepted'] for x in rows),used_ids=used,retired_uncharged_ids=retired,unused_ids=[i for i in range(42600,42700) if i not in used],kani_budget=6,kani_invocations=kanis,current_modules=current,lean_receipts=rows,premises_removed=0,rows_removed=[],target_established=False)
(E/'RESULTS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['lean_compile_attempts','lean_accepted','lean_failed','retired_uncharged_ids','unused_ids']},indent=2))
