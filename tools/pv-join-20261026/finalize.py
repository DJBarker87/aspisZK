"""Validate retained evidence and report scope. Never invokes a compiler."""
from pathlib import Path
import hashlib,json,re,subprocess
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026';l=e/'local';lean=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads((l/'26500.json').read_text())]
rows += [json.loads(p.read_text()) for p in sorted(l.glob('*-receipt.json'))]
assert len(rows)==100,len(rows)
allowed={'propext','Classical.choice','Quot.sound'};validated=[];latest={}
for x in rows:
 a=x['attempt'];status=x.get('exit_status',x.get('exit'))
 if a!=26500:
  assert sha(l/x['source_snapshot'])==x['source_sha256'],a
  raw=(e/f'local-{a}.log').read_text()
 else:raw=(l/'26500-out.log').read_text()
 reports=x.get('print_axioms',[])
 if status==0:
  assert 'sorryAx' not in raw and ': error:' not in raw,a
  for report in reports:
   if 'depends on axioms:' in report:
    axioms={s.strip() for s in report.split('depends on axioms: [')[1].split(']')[0].split(',') if s.strip()}
    assert axioms<=allowed,(a,axioms)
 if a!=26500:
  m=x['module'].split('/')[-1]
  if m not in latest or a>latest[m]['attempt']:latest[m]=x
 validated.append(dict(attempt=a,target=x.get('module',x.get('target')),exit=status,wall_seconds=x.get('wall_seconds',x.get('wall')),peak_rss_bytes=x.get('peak_rss_bytes'),swaps=x.get('swaps',x.get('swap')),source_revision=x['source_revision'],source_sha256=x['source_sha256'],deps_fingerprint=x['deps_fingerprint'],axiom_report_count=len(reports),receipt=f'local/{a}-receipt.json' if a!=26500 else 'local/26500.json'))
accepted=[]
for f in sorted(lean.glob('PV_Join_*.lean')):
 if f.stem=='PV_Join_Inspect':
  assert sha(f)==rows[0]['source_sha256'];continue
 x=latest[f.stem];assert x['exit_status']==0 and x['source_sha256']==sha(f),f
 accepted.append(dict(module='R1Z.'+f.stem,source=str(f.relative_to(r)),sha256=sha(f),attempt=x['attempt']))
closures={}
for a in [26576,26602,26603]:
 raw=(e/f'local-{a}.log').read_text()
 for root,body in re.findall(r'JOIN_CLOSURE ([\w.]+): \[([\s\S]*?)\]',raw):
  if a==26603 and root=='R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed':continue
  closures[root]=dict(attempt=a,laws=[s.strip() for s in body.split(',') if s.strip()])
assert len(closures['R1Z.PV_Join_AggregateCaller.refinement_of_data']['laws'])==26
assert closures['R1Z.PV_Join_PublicCaller.refinement_of_data']['laws']==['R1Z.PV_CB_Op229Source.op229_source']
assert not closures['R1Z.ProverRwP6BodyData.refinement_of_data']['laws']
assert not closures['R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed']['laws']
base='17fb86ac74019ca0553285dee0eeb9ce97642d6a';frozen=['crates','programs','docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6BodyData.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean']
assert not subprocess.check_output(['git','diff','--name-only',base,'HEAD','--',*frozen],cwd=r)
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
(e/'COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],cwd=r,text=True))
(e/'receipts.json').write_text(json.dumps(validated,indent=2)+'\n')
(e/'proof-closures.json').write_text(json.dumps(closures,indent=2)+'\n')
summary=dict(branch='codex/pv-join-20261026',source_revision=revision,base_revision=base,lean_attempts=100,lean_passes=sum(x['exit']==0 for x in validated),lean_failed_or_terminated=sum(x['exit']!=0 for x in validated),local_guard_refusals=[26520,26522,26524],host_refusals=[26574],kani_runs=0,kani_budget=10,accepted_new_modules=accepted,aggregate_source_law_declarations=26,candidate_source_callbacks_before=31,candidate_source_callbacks_after=30,candidate_removed_op=229,original_p6_changed=False,original_headline_changed=False,headline_premises_removed=0,headline_joined_rows=[],final_audit=dict(attempt=26603,exit=1,new_theorem_standard_axiom_reports=55,reason='Missing headline import in diagnostic audit; corrected pending draft not compiled'),peak_rss_bytes=max(x['peak_rss_bytes'] for x in validated),swaps=sum(x['swaps'] for x in validated),fixtures=dict(default='security-model data-equation non-vacuity NOT established',devnet='security-model data-equation non-vacuity NOT established'),shipped_code_changed=False,coherent_release_replay=False,target_established=False,next_unused_id=26604,stopped_by='100 actual Lean compile attempts exhausted; host assigned range also refused. No native/shipped-source counterexample claimed.',next_deliverable='Compile corrected audit under renewed allocation, then install the exact selected caller into native BodySourceLaw/runtime and the headline with actual data/fixture/world association.')
(e/'FINAL-REPORT.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['lean_attempts','lean_passes','lean_failed_or_terminated','peak_rss_bytes','swaps','headline_premises_removed','final_audit']},indent=2))
