"""Resolve the original Funs dependency and record the h6' rebuild decision."""
from pathlib import Path
import subprocess,json,hashlib,re
P=Path('docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean');rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();s=P.read_text();assert subprocess.check_output(['git','show',rev+':'+str(P)]).decode()==s
record=dict(module='R1Z.ProverRwFullFuns',path=str(P),blob=subprocess.check_output(['git','rev-parse',rev+':'+str(P)],text=True).strip(),sha256=hashlib.sha256(s.encode()).hexdigest(),authority='h5 HEAD; absent EJR and recorded freeze',imports=re.findall(r'^import (\S+)',s,re.M),tracked_conflicts=[])
code='''from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028');A=RECORD;source=SOURCE;revision=REVISION
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
shared=H.parent/'aspis-joint-20261019';changes=[]
for m in ['R1Z/ProverRwFullTypes','R1Z/ProverRwFullExternalFuns']:
 own=H/'lean'/(m+'.lean');other=shared/'sources'/(m+'.lean')
 assert sha(own)==sha(other)
 mine=H/'lean-objects'/(m+'.olean');theirs=shared/'objects'/(m+'.olean')
 changes.append(dict(module=m,source_sha256=sha(own),same_source=True,own_object_sha256=sha(mine),shared_object_sha256=sha(theirs),reuse_allowed=sha(mine)==sha(theirs)))
assert (shared/'sources/R1Z/ProverRwFullFuns.lean').read_text()==source
p=H/'lean/R1Z/ProverRwFullFuns.lean';p.parent.mkdir(exist_ok=True);p.write_text(source)
x=json.loads((H/'project-resolution-resume18.json').read_text());x['revision']=revision;x['modules'][A['module']]=A;(H/'project-resolution-resume18.json').write_text(json.dumps(x,indent=2)+'\\n')
(H/'resume18/RUNJOIN-COHORT-RECONCILIATION-D557.json').write_text(json.dumps(dict(authority=A,source_revision=revision,conflicts=changes,decision='h6-prime: same sources, conflicting object build instances; rebuild ONLY Funs in own cohort; never mix shared object',pre_elaboration_failure=79726,failed_source_unchanged=True,allowed_ruling='u-prime genuine missing dependency object; corrected by separately compiled, source-pinned dependency',expected_time='one generated dependency elaboration; no concrete arithmetic evaluation or proof generation'),indent=2)+'\\n')
print('staged original dependency; shared objects not reused')
'''.replace('RECORD',repr(record)).replace('SOURCE',repr(s)).replace('REVISION',repr(rev))
print(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True),end='')
