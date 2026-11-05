from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();sources=[E.parent/'ledger11-20261107/NII_AUDIT_ROOTS.json',E.parent/'slice-d-entry4-20261106/NHY_AUDIT_ROOTS.json'];required=set();inputs=[]
for p in sources:
 x=json.loads(p.read_text());required.update(x['roots']);inputs.append(dict(path=str(p.relative_to(E.parents[1])),sha256=H(p.read_bytes()),roots=len(x['roots'])))
measured={};bad=[]
for i in range(7):
 p=E/'NIM_audit'/('batch'+str(i))/('proof'+str(i)+'.json');x=json.loads(p.read_text())
 for j,r in enumerate(x['results']):
  assert r['root']not in measured
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
  measured[r['root']]=dict(attempt=f'NIM_L{34+i:03}',result=str(p.relative_to(E)),index=j,raw_axioms=r['walked_axioms'])
  if not r['equal']:bad.append(r)
assert required<=set(measured)
assert len(bad)==1 and bad[0]['root']=='NHC_DecodeModel.decoder_error' and bad[0]['collect_axioms']==[]
selected=set(json.loads((E/'NIM_AUDIT_ROOTS.json').read_text())['roots']);missing=selected-set(measured);assert len(missing)==103 and all('.'not in n for n in missing) and not missing&required
x=dict(status='PASS_REQUIRED_RAW_ROOT_COVERAGE',required_roots=len(required),measured_raw_roots=len(measured),inputs=inputs,required_without_results=[],invalid_extra_selectors=sorted(missing),extra_measured_roots=sorted(set(measured)-required),raw_summary_findings=bad,ruling="C3-BIN (ab')(3): raw walk authoritative; standard raw axioms pass despite collectAxioms disagreement",historical_batch_exits={'NIM_L039':1,'NIM_L040':1},verdicts_rewritten=False,new_prover_runs=0,coverage={n:measured[n]for n in sorted(required)})
(E/'NIM_ROOT_RECONCILIATION.json').write_text(json.dumps(x,indent=1)+'\n')
roots=sorted(required);(E/'NIM_AUDIT_ROOTS_CORRECTED.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i*len(roots)//7:(i+1)*len(roots)//7]for i in range(7)],executed=False,note='Corrected future selectors only. Every root already measured under original selectors; see NIM_ROOT_RECONCILIATION.json.'),indent=1)+'\n')
print(json.dumps({k:v for k,v in x.items()if k not in ['coverage','invalid_extra_selectors','inputs','raw_summary_findings']}))
