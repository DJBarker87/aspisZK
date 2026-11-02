"""Check focused receipts, exact statements, retained residuals and budgets."""
from pathlib import Path
import json,hashlib,re,subprocess,lzma
R=Path('evidence/pv-b3p6-20261028/resume18');sha=lambda b:hashlib.sha256(b).hexdigest()
inv=json.loads((R/'D557-final-host-inventory.json').read_text())
for n,h in inv['hashes'].items():
 p=R/n.removeprefix('resume18/');b=p.read_bytes()if p.exists()else lzma.decompress(p.with_name(p.name+'.xz').read_bytes());assert sha(b)==h,n
rows=[];accepted={}
for p in sorted(R.glob('lean-797*/receipt/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt']
 if a<79717:continue
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']==0 and r['shared_sources_written']is False
 assert sha((p.parent.parent/'source.lean').read_bytes())==r['source_sha256']
 assert sha(subprocess.check_output(['git','cat-file','blob',r['project_source_authority']['blob']]))==r['source_sha256']
 assert json.loads((p.parent.parent/'reservation.json').read_text())['allowed']is True
 assert json.loads((p.parent.parent/'barrier.json').read_text())['allowed']is True
 log=(p.parent/'stdout.log').read_text()+(p.parent/'stderr.log').read_text()
 if r['exit_status']==0:
  assert 'sorryAx'not in log and 'error:'not in log
  ax=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
  assert all(set(v.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for v in ax)
  if r['module']!='R1Z.ProverRwFullFuns':assert ax or 'does not depend on any axioms'in log
  accepted[r['module']]=r
 rows.append({k:r[k]for k in ['attempt','module','source_sha256','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','print_axioms']})
assert len(rows)==15 and sum(r['exit_status']==0 for r in rows)==11
assert '0 loaded units listed'in inv['scopes']
assert sha(Path('tools/pv-b3p6-20261028/compile_resume18_extended.py').read_bytes())==inv['guard_sha256']
log=(R/'lean-79731/receipt/stdout.log').read_text();assert len(re.findall(r'depends on axioms: \[',log))==14
assert 'DeployedWrapper557 base ops'in log
x=json.loads((R/'EXACT-BRIDGE-STATEMENT-D557.json').read_text());assert x['exact_utf8_after_whitespace']and not x['unconditional_deployed_bridge']
x=json.loads((R/'CLOSURE-RESIDUALS-D557.json').read_text());assert len(x['full_std_closure']['missing'])==16 and x['premises']==dict(removed=[],added=[],weakened=[])
pins=json.loads((R/'B3Q-SOURCE-PINS-D557.json').read_text())
for p in pins['modules']:assert sha(Path(p['path']).read_bytes())==p['sha256']
reuse=json.loads((R/'B3Q-COHORT-REUSE-D557.json').read_text());assert len(reuse['decisions'])==25 and reuse['conflicts']==[]
repair=json.loads((R/'RUNJOIN-COHORT-RECONCILIATION-D557.json').read_text());assert all(r['same_source']and not r['reuse_allowed']for r in repair['conflicts'])
exception=json.loads((R/'environment-exceptions-D557.json').read_text());assert len(exception)==1 and exception[0]['failed_attempt']==79726
assert next(r for r in rows if r['attempt']==79726)['source_sha256']==next(r for r in rows if r['attempt']==79729)['source_sha256']
t=json.loads((R/'TALLY-resume18.json').read_text());assert t['lean_attempts']==112 and t['next_unused_id']==79732
out=dict(target='NOT ESTABLISHED: unconditional deployed selected_callback remains open',before=dict(local_associations=36,selected_callback='UNDISCHARGED'),after=dict(local_associations=36,joint_local_links=True,partial_dependency_entries=9,frontier_vec_port=True,composed_source_continuation=True,original_runjoin_conditional_consumer=True,selected_callback='UNDISCHARGED'),new_receipts=rows,accepted=len(accepted),failed_no_credit=[r['attempt']for r in rows if r['exit_status']!=0],new_extraction=0,new_kani=0,budget=dict(lean_remaining=180-t['lean_attempts'],extraction_remaining=22,kani_remaining=25,next_lean=79732,audits_unspent=[79797,79798,79799]),peak_rss_kib=max(r['peak_rss_kib']for r in rows),longest_wall_seconds=max(r['wall_seconds']for r in rows),axioms='14 integrated theorem outputs; only propext/Classical.choice/Quot.sound',premises_removed=[],premises_added=[],full_frozen_manifest='not run: full deployed cone still incomplete',checkpoint='context checkpoint, not budget exhaustion',guard_sha256=inv['guard_sha256'],host_artifacts_verified=len(inv['hashes']))
(R/'verification-summary-D557.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['target','accepted','failed_no_credit','budget','peak_rss_kib','longest_wall_seconds','host_artifacts_verified']}))
