"""Retain provenance/status from existing receipts; never runs Lean or an audit."""
from pathlib import Path
import json,hashlib,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2]
records=[json.loads((L/f'receipt-{a}.json').read_text()) for a in range(55148,55183)]
accepted=[r['attempt'] for r in records if r['accepted']];failed=[r['attempt'] for r in records if not r['accepted']]
mods=[r['target'] for r in records if r['accepted'] and r['target']!='PV_LIB_SPEC_RawAuditSession13']
s={'base_revision':'f794c7fe857c2dbf16aa1dc3268e40033f7316a9','branch':'codex/pv-lib-spec-20261107','accepted_focused':accepted,'failed_focused':failed,'raw_attempt':55191,'full_task_complete':False,'successful_original_history':False,'full_source_joint_witness_inhabited':False,'full_joint_contradiction_proved':False,'physical_stack_pairing_proved':False,'concrete_Values_binding_discharged':False,'integrated_v2_source_adequacy_proved':False,'full_contracts_rebound':False,'nonvacuous_same_history_exports':False,'entry_with_native_backing_pre_proved':True,'local_C11_repair_installed':True,'runtime':'PV_LIB_SPEC_PrefixNative13','history':'PV_LIB_SPEC_PrefixHistory13.original','environment':'PV_LIB_SPEC_PrefixEnvironment13','hook454_bound':False,'stack_size295_bound':False,'row_closures':[],'endpoint_premises_removed':[],'endpoint_premises_added':[],'T_changes':[],'next_lean':55183,'next_raw':55192,'local_pre_id_input_errors':['builder generator used statement list index instead of source id; corrected','missing generated source scp; no host attempt/turn taken until generated']}
(L/'SESSION13_STATUS.json').write_text(json.dumps(s,indent=2)+'\n')
provenance=[]
for r in records:
 row={k:r[k] for k in ['attempt','target','source_revision','source_sha256','accepted','exit','wall','peak_rss_kbytes','swaps','axioms_summary_based']}
 row['path']='lean/'+r['target']+'.lean'
 if r['accepted']:
  c=subprocess.check_output(['git','log','-1','--diff-filter=A','--format=%H','--',row['path']],cwd=R,text=True).strip()
  b=subprocess.check_output(['git','show',c+':'+row['path']],cwd=R)
  assert hashlib.sha256(b).hexdigest()==r['source_sha256']
  row['passing_source_commit']=c
 provenance.append(row)
(L/'SESSION13_PROVENANCE.json').write_text(json.dumps({'attempts':provenance},indent=2)+'\n')
(L/'SESSION13_VALIDATION.json').write_text(json.dumps({'records':records},indent=2)+'\n')
(L/'SESSION13_MAP_DELTA.json').write_text(json.dumps({'shared_map_edited':False,'full_contracts_rebound':False,'row_closures':[],'new_modules':mods,'runtime':s['runtime'],'history':s['history'],'slots':{'atomic127/129/528':'Current source-store value binding installed; original caller history OPEN','TLS469/Cell18':'Exact source token and initialized source/physical value binding; local poll checked; original history OPEN','Cell289/371':'Source return values bound; bool ACTIVE physical mirror installed; source history OPEN','native452':'Adopted COUNTER address/CAS-success schedule and concrete counter1->2; original prefix OPEN','native360/457':'C11 physical count mirror alongside unchanged v2 source actions; source/physical operand agreement still to derive THERE','native269':'Exact frozen Builder constructor None/None/no_hooks=false; source454 still required','native295/453/454':'Bindings OPEN; do not promote default-stack helper to original branch','Values/full-table':'VALUE-only parameter and PARTIAL v2 retained; complete concrete bindings/source adequacy OPEN','physical_stack':'Original correspondence OPEN; finite session12 map retained as data','ThreadInit14756/OwnInit':'Successful same-history exports and complete joint witness/negation OPEN'}},indent=2)+'\n')
(L/'SESSION13_COMMITS_BEFORE_FINAL.txt').write_text(subprocess.check_output(['git','log','--oneline',s['base_revision']+'..HEAD'],cwd=R,text=True))
print('Retained',len(accepted),'passing compiles and',len(failed),'failures;',len(mods),'semantic modules; full task OPEN')
