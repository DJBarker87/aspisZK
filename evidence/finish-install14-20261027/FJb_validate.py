from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];valid=[];failed=[];missing=[]
for n in range(1,101):
 a=f'FJb_{n:03}';q=P/a/'receipt.json'
 if q.is_file():
  x=json.loads(q.read_text());x['receipt_path']=str(q.relative_to(R));receipts.append(x)
  (valid if x.get('exit_status')==0 else failed).append(a)
 else:missing.append(a)
current=[]
for p in sorted((R/'lean').glob('FJb_*.lean')):
 h=sha(p);matches=[]
 for a in valid:
  f=P/a/'sources'/p.name
  if f.is_file() and sha(f)==h:matches.append(a)
 current.append(dict(module=p.stem,source_sha256=h,passing_attempts=matches))
for x in receipts:
 if x.get('exit_status')==0:
  assert not any('sorryAx' in s for s in x.get('print_axioms',[])),x
out=dict(charged_attempts=len(list(P.glob('FJb_[0-9][0-9][0-9].json'))),compiler_starts=len(receipts),passes=len(valid),failures=len(failed),precompiler_stops=missing,valid_attempts=valid,failed_attempts=failed,current_sources=current,unvalidated=[x['module'] for x in current if not x['passing_attempts']],kani_runs=0,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),release_claim=False)
(P/'FJb_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['current_sources','valid_attempts','failed_attempts']},indent=2))
