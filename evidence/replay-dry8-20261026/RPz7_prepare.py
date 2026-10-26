from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];old=R/'evidence/replay-dry6-20261026'
p=json.loads((old/'RPz5_source-plan.json').read_text());u=json.loads((old/'RPz5_tx1-probe-source-plan.json').read_text());s=json.loads((old/'RPz5_state.json').read_text())['state'];us=json.loads((old/'RPz5_tx1-probe-state.json').read_text())['state']
a={'AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs'}
for m in p['order']:
 if any(n in a for n in p['modules'][m]['imports']):a.add(m)
reuse={m:('RPz5_union_overlay' if us.get(m)=='passed' else 'RPz5_overlay') for m in p['order'] if (m not in a and s.get(m)=='passed') or us.get(m)=='passed'}
missing=[m for m in p['order'] if m not in reuse];mapping={m:'RPz7_'+m.replace('.','_') for m in missing}
assert len(set(mapping.values()))==len(mapping)
# Explicitly selected legacy Phase use sites; other verifier namespaces remain intact.
legacy={'S1SemanticPrefixModelV1','S1SemanticFinishModelV1','S1SemanticFinishBoundsV1','S1SemanticVerifyReachabilityV1','S1SemanticFinishRootsV1','S1SemanticCodeFinishV1','S1SemanticCodeVerifyV1','S1SemanticCodeFinishExactV1','S1SemanticCodeVerifyExactV1','GExp_FinishAssociation','GExp_VerifyAssociation','S1SemanticBudgetV1'}
rows=[];uses=[]
for m in missing:
 x=p['modules'][m];src=R/x['source'];t=src.read_text();assert hashlib.sha256(src.read_bytes()).hexdigest()==x['sha256']
 if m=='S1SemanticPhaseV1':imports=['Init','RPz7_PhaseIso']
 else:
  for n,new in mapping.items():
   if n in x['imports']:t=re.sub(r'(?m)^(import\s+)'+re.escape(n)+r'\s*$',lambda z:z[1]+new,t)
  if m in legacy:
   for i,l in enumerate(t.splitlines(),1):
    if 'verifier.Phase' in l:uses.append({'module':m,'line':i,'original':l,'replacement':l.replace('verifier.Phase','RPz7_PhaseIso.Phase')})
   t=t.replace('verifier.Phase','RPz7_PhaseIso.Phase')
  imports=[mapping.get(n,n) for n in x['imports']]
  (E/(mapping[m]+'.lean')).write_text(t)
 rows.append(dict(original=m,module=mapping[m],source=str((E/(mapping[m]+'.lean')).relative_to(R)),imports=imports,original_source=x['source'],original_sha256=x['sha256']))
# PhaseIso is the first target, then the replacement, then topologically ready dependents.
plan=dict(revision=p['revision'],order=p['order'],reuse=reuse,rows=rows,mapping=mapping,legacy_phase_uses=uses,larger_producer_sources={m:u['modules'][m] for m in ['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs']},budget=1498,open_provenance='historical e5c Tx1 extraction; full frozen D188 extraction provenance unestablished')
(E/'RPz7_plan.json').write_text(json.dumps(plan,indent=2)+'\n')
# One complete job-owned namespace view; retained views/objects are never modified.
from RPz7_attempt import ssh,B
payload="""from pathlib import Path
import json,hashlib
B=Path(%r);reuse=json.loads(%r);out={}
view=B/'RPz7_overlay';view.mkdir(exist_ok=False)
for m,v in reuse.items():
 p=B/v/(m.replace('.','/')+'.olean');assert p.is_file(),p
 for ext in ['', '.server','.private','IR']:
  src=p.with_suffix('.ir') if ext=='IR' else Path(str(p)+ext)
  if not src.is_file():continue
  dst=view/src.relative_to(B/v);dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src.resolve())
  out[str(dst)]={'target':str(src.resolve()),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'bytes':src.stat().st_size}
(B/'RPz7_overlay-base.json').write_text(json.dumps(out,indent=2)+'\\n')
print(json.dumps({'modules':len(reuse),'artifacts':len(out)}))
"""%(B,json.dumps(reuse))
r=ssh('python3 -',payload);assert r.returncode==0,r.stderr
from RPz7_attempt import collect
collect('RPz7_overlay-base.json')
print(r.stdout,'missing',len(rows))
