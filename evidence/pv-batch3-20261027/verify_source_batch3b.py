from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
p=json.loads((H/'resume-source.json').read_text());bad=[];matches=0
for n,h in p['files'].items():
 q=H/'source'/n
 a=hashlib.sha256(q.read_bytes()).hexdigest() if q.exists() else None
 if a!=h and n!='crates/aspis-prover/src/host_forest.rs':bad.append(dict(path=n,expected=h,actual=a))
 elif a==h:matches+=1
out=dict(unchanged_inputs_checked=matches,mismatches=bad,changed_path='crates/aspis-prover/src/host_forest.rs',changed_sha256=hashlib.sha256((H/'source/crates/aspis-prover/src/host_forest.rs').read_bytes()).hexdigest())
(H/'batch3b-source-verification.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
