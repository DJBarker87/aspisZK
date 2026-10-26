"""Inventory exact source-law statements and distinguish counts from binders.
No compiler or build infrastructure is invoked. No closure credit from imports.
"""
from pathlib import Path
import hashlib,json,re,subprocess
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=r/'evidence/pv-join-20261026'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-next/final-state.json'
refs=json.loads(old.read_text())['selector']['remaining_source_successful_body_refs']
p6=sorted(set(refs)-{51,120,225,254});p8=sorted(set(p6)-{78,231,247,255})
assert len(p6)==35 and len(p8)==31
rows=[]
for f in sorted([*p.glob('PV_CB_*.lean'),*p.glob('PV_CB3_*.lean')]):
 s=f.read_text()
 for m in re.finditer(r'\btheorem (op(\d+)_source)\b',s):
  tail=s[m.start():];end=tail.find('\n#print axioms');tail=tail if end<0 else tail[:end]
  stmt=tail.split(' :=',1)[0].strip();n=int(m[2]);rows.append(dict(module='R1Z.'+f.stem,theorem=m[1],op=n,statement=stmt,source=str(f.relative_to(r)),sha256=sha(f),in_historical_p6_remaining=n in p6,in_historical_p8_remaining=n in p8,endpoint_joined=False))
root=p/'PrivacyR1HeadlineDeployedReal.lean';body=p/'ProverRwP6BodyData.lean'
x=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),historical_baseline=dict(path=str(old.relative_to(r)),sha256=sha(old),p6_remaining=p6,p8_remaining=p8,warning='Historical source-interpretation counts, not binder counts or native assumptions.'),callback_source_laws=rows,unique_ops=sorted({x['op'] for x in rows}),historical_overlap=sorted({x['op'] for x in rows}&set(p8)),roots={f.stem:dict(path=str(f.relative_to(r)),sha256=sha(f),imports=re.findall(r'^import (.*)$',f.read_text(),re.M)) for f in [root,body]},endpoint_premises_removed=0,target_established=False)
(e/'source-inventory.json').write_text(json.dumps(x,indent=2)+'\n');print(len(rows),'source-law declarations; historical31 overlap:',x['historical_overlap'])
