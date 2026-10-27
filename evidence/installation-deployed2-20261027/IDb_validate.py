"""Validate final source-to-passing-receipt matches; no prover launch."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent; R=E.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
modules={'IDb_Components':3,'IDb_Deployed':5,'IDb_Nonvacuity':6,'IDb_Audit':7,'IDb_Residual':9}
valid=[]
for mod,n in modules.items():
 p=R/'lean'/(mod+'.lean'); d=E/f'IDb_{n:03}'
 x=json.loads((d/'receipt.json').read_text())
 assert x['exit_status']==0
 assert sha(p)==sha(d/'sources'/p.name)
 assert x['source_hashes'][p.name]==sha(p)
 reports=x['print_axioms']; assert reports
 for report in reports:
  assert 'sorryAx' not in report,report
  a=report[report.index('[')+1:report.rindex(']')]
  a=re.sub(r'\.\{[^}]*\}','',a)
  assert set(a.split(', '))<= {'propext','Classical.choice','Quot.sound'},a
 text=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option (maxHeartbeats|maxRecDepth)',text,re.M)
 valid.append(dict(module=mod,attempt=f'IDb_{n:03}',source_sha256=sha(p),axioms=reports))
rows=[]
for p in sorted(E.glob('IDb_*/receipt.json')):
 x=json.loads(p.read_text());rows.append({k:x.get(k) for k in ['attempt','command','sources','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
assert len(rows)==9
out=dict(lean_attempts=9,budget=40,kani_runs=0,final_modules=valid,attempts=rows,accepted_axioms=['propext','Classical.choice','Quot.sound'],rejected_attempts=['IDb_001','IDb_002','IDb_004','IDb_008'],memory_kills=[],timeout_replacement={'IDb_008':'IDb_009: split whole reduction into RowShape and Uni projections'},scope=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),lean_memory_flag='-M7000',package_replay=False,release_claim=False)
(E/'IDb_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
print('Validated five current modules against passing exact-source receipts; 9/40 Lean, 0 Kani.')
