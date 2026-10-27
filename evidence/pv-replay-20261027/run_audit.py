"""After the coherent closure, compile the diagnostic once under the same caps."""
import json,hashlib
from pathlib import Path
import run_host as replay
P=replay.P;E=replay.E
rs={r['module']:r for r in map(json.loads,(E/'results.jsonl').read_text().splitlines())}
assert len(rs)==len(replay.nodes)
assert all(r['status'] in ['compiled','reused'] for r in rs.values()),'closure incomplete: do not audit stale headline objects'
m='PV_ReplayAudit';p=P/'sources'/(m+'.lean')
n=dict(module=m,source_path='evidence/pv-replay-20261027/PV_ReplayAudit.lean',source_sha256=replay.sha(p),deps_fingerprint=hashlib.sha256(p.read_bytes()).hexdigest())
deps=[replay.dep_record(m) for m in ['R1Z/PrivacyR1HeadlineDeployedReal','R1Z/PrivacyR1HeadlineV2','Lean/Elab/Command']]
assert all(d is not None for d in deps)
closure_revision=replay.plan['revision']
replay.plan['revision']=(P/'audit-revision.txt').read_text().strip()
r=replay.compile_one(m,n,deps)
r['closure_source_revision']=closure_revision
replay.dump(E/'audit-result.json',r)
