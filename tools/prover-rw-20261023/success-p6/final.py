"""Read-only final continuation audit; does not launch proof jobs or change infrastructure."""
from pathlib import Path
import json, hashlib, subprocess, re
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p6'
sha=lambda b:hashlib.sha256(b).hexdigest()
summary=json.loads((e/'summary.json').read_text())
accepted=[]
for p in sorted((r/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('ProverRwP6*.lean')):
 matches=[x for x in summary['attempts'] if x['exit']==0 and (e/f"{x['attempt']}.lean.txt").read_bytes()==p.read_bytes()]
 assert matches,p
 accepted.append(dict(path=str(p.relative_to(r)),sha256=sha(p.read_bytes()),attempt=matches[-1]['attempt']))
roots=[]
base='e1804622780375b9eb206f2505fa4dc83be5939c'
for name in ['ProverCommitDeployedFuel22','PrivacyR1HeadlineDeployedReal']:
 p=r/f'docs/research/v8-r0-zk-20261009/lean/R1Z/{name}.lean'
 assert p.read_bytes()==subprocess.check_output(['git','show',base+':'+str(p.relative_to(r))],cwd=r)
 roots.append(dict(path=str(p.relative_to(r)),sha256=sha(p.read_bytes()),unchanged=True))
audit=json.loads((e/'14069-receipt.json').read_text())
assert audit['exit_status']==0
objects={d['module']:d['object_sha256'] for d in audit['dependencies']}
for row in accepted:
 if row['attempt']==14069:continue
 module='R1Z.'+Path(row['path']).stem
 assert module in objects,module
reports=audit['print_axioms']
assert len(reports)==90
# Keep all historical native evidence and constructor-domain limitations explicit.
# No reruns: enumerate retained command receipts from both old and continuation paths.
references={sha(p.read_bytes()):p.name for p in e.glob('proof-reference-version-*.rs.txt')}
current=r/'tools/prover-rw-20261023/success-p6/proof/lib.rs'
(e/'proof-reference-final.rs.txt').write_bytes(current.read_bytes())
references[sha(current.read_bytes())]='proof-reference-final.rs.txt'
native=[]
for parent in ['native','translation']:
 for p in sorted((e/parent).glob('*/preflight.json')):
  pre=json.loads(p.read_text());d=p.parent
  time=(d/'time.log').read_text() if (d/'time.log').exists() else ''
  status=re.search(r'Exit status: (\d+)',time)
  command=pre['target']
  h=pre['source_sha256'].get('tools/prover-rw-20261023/success-p6/proof/lib.rs')
  row=dict(path=str(d.relative_to(r)),command=command,kind='Kani' if 'kani' in command else 'extraction',exit=int(status[1]) if status else None,source_revision_label=pre['source_revision'],proof_reference_sha256=h,reference_snapshot=references.get(h))
  if row['kind']=='Kani' and row['exit']==0:assert row['reference_snapshot'],row
  native.append(row)
continuation=[x for x in summary['attempts'] if x['attempt']>=14005]
assert len(continuation)==65 and all(x['exit'] is not None for x in continuation)
result=dict(base_revision=base,audited_revision=audit['source_revision'],accepted_lean_sources=accepted,root_sources=roots,final_audit_attempt=14069,final_axiom_reports=len(reports),final_dependency_objects=len(objects),lean_compiles=summary['lean_compiles'],lean_passes=summary['passes'],continuation_lean_attempts=65,continuation_lean_budget=65,continuation_lean_remaining=0,continuation_kani_runs=7,continuation_kani_budget=7,continuation_kani_remaining=0,next_unused_env_J=14070,native_evidence=native,new_candidate_source_or_P6_entries=[225,51,120,254],remaining_source_entries=35,root_premises_removed=0,target_established=False,stopped_by='Assigned continuation budget exhausted, counting attempts before capacity resume',remaining='Compression shipped/reference equivalence; remaining35 callbacks and native carrier/ABI/compiler/artifact adequacy; complete proof/audit data equation; concrete PrefixContract/BodyContract; E1/E2 and native effects; ordered ROM/TLS; real RunJoin',scope='Focused cached source/axioms audit only; no coherent frozen release replay, native gate rerun, or privacy claim')
(e/'final-state.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['lean_compiles','lean_passes','continuation_lean_remaining','final_axiom_reports','final_dependency_objects','remaining_source_entries','root_premises_removed']},indent=2))
