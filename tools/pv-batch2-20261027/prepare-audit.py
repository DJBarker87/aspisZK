"""Freeze accepted current sources, archive rejected/unmeasured drafts, prepare
three new audit modules. Does not launch a compiler or write any shared source.
"""
from pathlib import Path
import json,re,hashlib
E=Path('evidence/pv-batch2-20261027');L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
t=json.loads((E/'TALLY.json').read_text());assert t['lean_charged']==97
allowed={'propext','Classical.choice','Quot.sound'}
def reports(s):
 out=[]
 for m in re.finditer(r"^'([^'\n]+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",s,re.M):
  ax=[] if m[3] is None else [a.strip() for a in m[3].replace('\n',' ').split(',') if a.strip()]
  out.append(dict(declaration=m[1],axioms=ax))
 return out
latest={};all_receipts=[]
for a in t['attempts']:
 p=E/f"{a['id']}.json"
 if not p.exists():continue
 r=json.loads(p.read_text());r['axioms_parsed']=reports(r.get('axiom_output',''))
 r['standard_axioms']=all(set(x['axioms'])<=allowed for x in r['axioms_parsed'])
 r['formal_accepted']=r['exit_status']==0 and r['standard_axioms']
 latest[r['module']]=r;all_receipts.append(r)
kept=[];drafts=[]
for p in sorted(L.glob('PV_B2_*.lean')):
 if 'Audit' in p.name:continue
 m='R1Z/'+p.stem;r=latest.get(m);sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if r and r['formal_accepted'] and r['source_sha256']==sha:
  kept.append(dict(module=m,source_sha256=sha,attempt=r['attempt'],declarations=r['axioms_parsed'],dependency_objects=r['dependency_objects']))
 else:
  q=E/'drafts'/(p.name+'.txt');q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes());p.unlink()
  drafts.append(dict(module=m,source_sha256=sha,path=str(q),reason='unmeasured draft' if not r else 'latest source not accepted',last_attempt=None if not r else r['attempt']))
assert all(set(d['axioms'])<=allowed for r in kept for d in r['declarations'])
(E/'ACCEPTED-PREFLIGHT.json').write_text(json.dumps(dict(kept=kept,drafts=drafts,charged=97,allowed_axioms=sorted(allowed),rejected_axiom_attempts=[r['attempt'] for r in all_receipts if not r['standard_axioms']]),indent=2)+'\n')
# Include each accepted module once in a family audit, then compose the two.
groups={'Sampler':[],'Weights':[]}
for r in kept:
 stem=r['module'].split('/')[-1]
 family='Weights' if any(x in stem for x in ['Weights','PV_B2_W_','PV_B2_Total_','PV_B2_Field_']) else 'Sampler'
 groups[family].append(r)
for family,rows in groups.items():
 out=''.join('import '+r['module'].replace('/','.')+'\n' for r in rows)+'\n'
 names=sorted({d['declaration'] for r in rows for d in r['declarations']})
 out+=''.join('#print axioms '+n+'\n' for n in names)
 (L/f'PV_B2_Audit{family}.lean').write_text(out)
root=['PV_B2_ordinary_sample.op250_source','PV_B2_GammaCarrier.source','PV_B2_RankDigits.source','PV_B2_LowDigits.source','PV_B2_WeightsTotal.points','PV_B2_FieldTotal.QM31_mul']
(L/'PV_B2_AuditManifest.lean').write_text('import R1Z.PV_B2_AuditSampler\nimport R1Z.PV_B2_AuditWeights\n\n'+''.join('#print axioms '+n+'\n' for n in root))
t['next_regular_id']=t['next_env_j_id'];t['next_env_j_id']=53597;t['next_id']=53597
(E/'TALLY.json').write_text(json.dumps(t,indent=2)+'\n')
print(json.dumps(dict(accepted_modules=len(kept),archived_drafts=len(drafts),declarations=sum(len(r['declarations']) for r in kept),next_audit_id=53597)))
