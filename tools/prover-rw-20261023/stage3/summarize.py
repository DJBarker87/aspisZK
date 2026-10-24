"""Produce an auditable local-stage ledger from immutable host receipts."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[3]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/stage3'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(E.glob('*-receipt.json')):
 x=json.loads(p.read_text()); log=x['time_log']
 def metric(label):
  m=re.search(re.escape(label)+r':\s*([^\n]+)',log);return m[1] if m else None
 x.update(wall_time=metric('Elapsed (wall clock) time (h:mm:ss or m:ss)'),peak_rss_kib=int(metric('Maximum resident set size (kbytes)')),swaps=int(metric('Swaps')))
 rows.append(x)
assert [r['attempt'] for r in rows]==list(range(11200,11212))
for r in rows:
 if r['exit_status']==0:
  assert all('sorryAx' not in a for a in r['print_axioms'])
# Ensure handoff source equals every final successful source, without a rebuild.
paths={
 'ProverRwSampler/Types':'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/continuation/generated-sampler/ProverRwSampler/Types.lean',
 'ProverRwSampler/Funs':'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwSampler/Funs.lean'}
for name in ['Arithmetic','Transport','Model']:
 paths['R1Z/ProverRwSampler'+name]='docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSampler'+name+'.lean'
for name in ['SemanticSampler','Stage3Audit']:
 paths['R1Z/ProverRw'+name]='docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw'+name+'.lean'
manifest=[]
for m,path in paths.items():
 last=next(r for r in reversed(rows) if r['module']==m)
 assert last['exit_status']==0 and last['source_sha256']==sha(R/path)
 manifest.append(dict(module=m,repo_source=path,source_sha256=sha(R/path),accepted_attempt=last['attempt'],deps_fingerprint=last['deps_fingerprint']))
audit=rows[-1];assert len(audit['print_axioms'])==20
quiet=json.loads((E/'quiet-preflight.json').read_text())
result=dict(status='Partial Stage 3; whole attempt equality and conjunct 1 remain open',base_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),production_revision='9c131667ca00f4daae78da6299b09a9fe0d00da9',new_lean_attempts=len(rows),lean_pass=sum(r['exit_status']==0 for r in rows),lean_fail=sum(r['exit_status']!=0 for r in rows),lean_budget=100,new_kani_runs=0,total_kani_runs=42,kani_budget=60,assigned_range=[11200,11399],next_attempt=11212,attempts=rows,focused_manifest=manifest,final_axioms=audit['print_axioms'],absolute_timing=dict(run=False,reason='Other populated capped jobs',load=quiet['load'],other_capped_job_count=len(quiet['other_capped_user_jobs'])),frozen_manifest_replayed=False,frozen_manifest_reason='Whole attempt source/model closure is not established; unchanged release gates not repeated',whole_attempt_proved=False,conjunct_1_proved=False,adopted=False)
(E/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['new_lean_attempts','lean_pass','lean_fail','new_kani_runs','next_attempt','whole_attempt_proved','conjunct_1_proved']}))
