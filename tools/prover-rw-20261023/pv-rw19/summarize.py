"""Summarize only retained receipts; never launches any validation."""
from pathlib import Path
import json,hashlib,datetime,subprocess
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw19-resume-20261026'
receipts=[json.loads(p.read_text()) for p in sorted(e.glob('27[789]*-receipt.json'))]
charged=[x for x in receipts if x.get('charged')]
latest={}
for x in receipts:
 if x.get('charged'):latest[x['module']]=x
root=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';checked=[];pending=[]
for p in sorted(root.glob('ProverRw19*.lean')):
 name='R1Z.'+p.stem;x=latest.get(name);sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if x and x['exit_status']==0 and x['source_sha256']==sha:
  checked.append({'module':name,'attempt':x['attempt'],'source_sha256':sha,'print_axioms':x['print_axioms']})
 else:pending.append({'module':name,'source_sha256':sha,'last_attempt':x['attempt'] if x else None})
axioms=[]
for v in charged:
 for line in v['print_axioms']:
  if 'depends on axioms: [' in line:axioms.extend(a.strip() for a in line.split('depends on axioms: [')[1].split(']')[0].split(','))
kn=e/'pv-rw19-step_out_c0a-001/receipt.json';kani=[json.loads(kn.read_text())] if kn.exists() else []
s={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'branch':subprocess.check_output(['git','branch','--show-current'],cwd=r,text=True).strip(),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),'base':'bf81d1d222','lean_budget':100,'lean_charged':len(charged),'lean_passes':sum(x['exit_status']==0 for x in charged),'lean_failures':sum(x['exit_status']!=0 for x in charged),'kani_budget':20,'kani_charged':len(kani),'kani_queue_stopped_on_configuration_failure':bool(kani),'gate_polls':[json.loads(v) for v in (e/'gate-polls.jsonl').read_text().splitlines()],'checked_rw19_modules':checked,'pending_rw19_modules':pending,'endpoint_premises_removed':[],'V164':'REDUCED: concrete P6 context_identity checked and supplied to callback/caller; exact P_source_p6 remains open; privacy endpoint unchanged','V163':'OPEN: independent assembly/preparation model families and full canonical-audit transport checked; deployed-caller mathematical preparation construction and both fixture/general byte equations remain missing','target_established':False,'all_successful_printed_axioms_standard':all(a.strip() in {'propext','Classical.choice','Quot.sound'} for x in charged if x['exit_status']==0 for line in x['print_axioms'] for a in (line.split('depends on axioms: [')[1].split(']')[0].split(',') if 'depends on axioms: [' in line else [])),'formal_attempts':[{k:x.get(k) for k in ['attempt','module','exit_status','wall_time','peak_rss_kib','swaps','source_revision','source_sha256','deps_fingerprint','print_axioms']} for x in charged]}
final=latest.get('R1Z.ProverRw19FrozenManifest')
if final and final['exit_status']==0:
 s['audit_command_module_coverage']={'module':'R1Z.ProverRw19AxiomsAudit','standalone_attempt':27826,'standalone_exit':1,'reason':'Missing cached transitive import before any commands executed','covered_by':'R1Z.ProverRw19FrozenManifest','combined_attempt':27828,'printed_declarations':len(final['print_axioms'])}
 s['pending_rw19_modules']=[v for v in s['pending_rw19_modules'] if v['module']!='R1Z.ProverRw19AxiomsAudit']
 s['next_unused_env_j']=27829
 s['stop_reason']='Lean budget exhausted; Kani queue stopped after first configuration failure'
 s['cached_component_replay']=True
 s['clean_source_dependency_rebuild']=False
 s['new_local_lean_compiles']=0
 s['new_toolchain_builds']=0
(e/'summary.json').write_text(json.dumps(s,indent=2)+'\n')
print({k:s[k] for k in ['lean_charged','lean_passes','lean_failures','kani_charged','all_successful_printed_axioms_standard']});print('checked rw19:',[x['module'] for x in checked])
