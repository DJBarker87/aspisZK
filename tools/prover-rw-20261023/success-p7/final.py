"""Read-only development handoff validation; never starts a proof or native job."""
from pathlib import Path
import hashlib,json,re,subprocess
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p7'
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((e/'summary.json').read_text());host=json.loads((e/'accepted-host-objects.json').read_text())
host={x['module']:x for x in host['targets']}
rows=[];axioms=[]
for p in sorted((r/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('ProverRwP7*.lean')):
 hits=[]
 for f in e.glob('*-receipt.json'):
  x=json.loads(f.read_text())
  if x['exit_status']==0 and (e/f"{x['attempt']}.lean.txt").read_bytes()==p.read_bytes():hits.append(x)
 assert hits,p
 x=hits[-1];module='R1Z.'+p.stem
 assert host[module]['source_sha256']==sha(p.read_bytes())
 text=p.read_text()
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b|native_decide|set_option\s+max(?:RecDepth|Heartbeats)',text,re.M)
 declarations=re.findall(r'^theorem\s+([^\s({]+)',text,re.M)
 assert len(declarations)==len(x['print_axioms']),(p,declarations,x['print_axioms'])
 for report in x['print_axioms']:
  assert 'sorryAx' not in report
  if 'depends on axioms:' in report:
   assert set(a.strip() for a in report.split('depends on axioms: [')[1].split(']')[0].split(','))<={'propext','Classical.choice','Quot.sound'}
 axioms+=x['print_axioms']
 rows.append(dict(path=str(p.relative_to(r)),sha256=sha(p.read_bytes()),accepted_attempt=x['attempt'],theorems=declarations,cached_object=host[module]))
assert len(rows)==24 and len(axioms)==85
roots=[]
base='e52b6bec0a'
for name in ['ProverCommitDeployedFuel22','PrivacyR1HeadlineDeployedReal']:
 p=r/f'docs/research/v8-r0-zk-20261009/lean/R1Z/{name}.lean'
 assert p.read_bytes()==subprocess.check_output(['git','show',base+':'+str(p.relative_to(r))],cwd=r)
 roots.append(dict(path=str(p.relative_to(r)),sha256=sha(p.read_bytes()),unchanged=True))
critical=['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/ct.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-core/src/r0/scalar.rs','crates/aspis-core/src/r0/domain.rs','crates/aspis-core/src/r0/transport.rs','crates/aspis-core/src/r0/transport_pads.rs','crates/aspis-statement/src/logup.rs','crates/aspis-statement/src/state_only_trace.rs']
for p in (e/'translation').glob('*/receipt.json'):
 x=json.loads(p.read_text())
 for q in critical:assert x['source_sha256'][q]==sha((r/q).read_bytes()),(p,q)
for name,snapshot in [('success-p7-reverse32-kani-001','reverse-reference.rs.txt'),('success-p7-coeff-table-kani-001','coefficient-table-reference.rs.txt')]:
 p=e/'translation'/name;x=json.loads((p/'receipt.json').read_text());assert x['exit_status']==0
 assert '1 successfully verified harnesses, 0 failures, 1 total' in (p/'stdout.log').read_text()
 assert x['source_sha256']['tools/prover-rw-20261023/success-p7/proof/lib.rs']==sha((e/snapshot).read_bytes())
 if 'table' in name:assert x['source_sha256']['tools/prover-rw-20261023/success-p7/proof/table.rs']==sha((e/'coefficient-table.rs.txt').read_bytes())
refusal=json.loads((e/'denied-14835/14835-admission-before.json').read_text());retry=json.loads((e/'denied-14835/retry-receipt.json').read_text())
assert refusal['allowed'] is False and retry['exit']==65 and 'already used' in retry['output']
assert not (e/'time-14835.log').exists()
pending=[dict(path=str(p.relative_to(r)),sha256=sha(p.read_bytes()),accepted=False) for p in sorted((e/'pending').glob('*.lean.txt'))]
assert len(pending)==4
assert s['lean_compiles']==35 and s['lean_passes']==24 and s['kani_runs']==3
result=dict(base_revision=base,proof_checkpoint=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),accepted_sources=rows,individual_accepted_axiom_reports=axioms,axiom_reports=85,root_sources=roots,pending=pending,new_candidate_source_or_P6_entries=[231,78],inherited_P6_entries=[225,51,120,254],remaining_callbacks=33,conjunct1_premises_removed=0,headline_premises_removed=0,target_established=False,budget=dict(Lean=100,Lean_used=35,Lean_remaining=65,Kani=15,Kani_used=3,Kani_remaining=12),stop='Existing launcher rejects permitted admission retry: attempt14835 already used,exit65. Rule5 stop; no infrastructure or replay-guard change.',denied_id=14835,next_unused_assigned_id=14836,scope='Individual focused source/axiom checks plus read-only cached object/source/root audit. No final combined axiom compile, coherent release replay, native artifact association or adoption claim.',remaining='Actual whole proof/audit security-model identity; compression shipped/reference correspondence;33 callbacks; native representations/ABI/compiler/artifact/effect adequacy; actual PrefixContract/BodyContract,E1/E2,ordered ROM/TLS and real RunJoin.')
(e/'final-state.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:result[k] for k in ['proof_checkpoint','axiom_reports','remaining_callbacks','conjunct1_premises_removed','budget','stop']})
