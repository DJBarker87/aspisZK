from pathlib import Path
import json,re,hashlib
from NBF_payloads import read_payload
E=Path(__file__).resolve().parent
runs=[]
for p in sorted(E.glob('NBF_K*/receipt.json')):
 r=json.loads(p.read_text());name=r['command'][r['command'].index('--harness')+1]
 runs.append(dict(attempt=r['attempt'],harness=name,exit_status=r['exit_status'],source_hashes=r['source_hashes'],receipt=str(p.relative_to(E))))
current=[]
for file,namespace in [('NBF_harness.rs','verifier::NBF_harness::'),('NBF_query.rs','verifier::candidate::NBF_query::')]:
 text=read_payload(file);sha=hashlib.sha256(text.encode()).hexdigest();key='NBF_src/crates/aspis-r1-cost-probe/src/'+file
 for name in re.findall(r'#\[kani::proof\][\s\S]*?\bfn (NBF_\w+)\s*\(',text):
  own=[r for r in runs if r['harness']==namespace+name]
  current.append(dict(harness=namespace+name,history=own,status='NOT_RUN' if not own else 'HISTORICAL_PASS' if any(r['exit_status']==0 for r in own) else 'FAILED_ONLY',current_payload_sha256=sha,current_payload_equals_last_run=bool(own and own[-1]['source_hashes'].get(key)==sha)))
(E/'NBF_HARNESS_STATUS.json').write_text(json.dumps(dict(note='Every historical result is valid only at its exact source patch/domain; unexecuted proof declarations are not passes. No final all-harness suite is claimed.',current_harnesses=current,historical_runs=runs),indent=2)+'\n')
print(json.dumps(dict(current_harnesses=len(current),not_run=sum(x['status']=='NOT_RUN' for x in current),historical_runs=len(runs))))
