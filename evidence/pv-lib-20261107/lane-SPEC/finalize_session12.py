"""Offline receipts/provenance only. Never launches a build or raw replay."""
from pathlib import Path
import json,subprocess,hashlib
L=Path(__file__).resolve().parent;R=L.parents[2]
records=[json.loads((L/f'receipt-{a}.json').read_text()) for a in range(55116,55148)]
accepted=[r['attempt'] for r in records if r['accepted']];failed=[r['attempt'] for r in records if not r['accepted']]
mods=[r['target'] for r in records if r['accepted'] and r['target']!='PV_LIB_SPEC_RawAuditSession12']
status={'base_revision':'966c928151970c37c0c4187255a3e3d3cffa66ba','branch':'codex/pv-lib-spec-20261107','accepted_focused':accepted,'failed_focused':failed,'raw_attempt':55190,'full_task_complete':False,'successful_original_history':False,'full_source_joint_witness_inhabited':False,'full_joint_contradiction_proved':False,'physical_stack_pairing_proved':False,'local_stack_codec_repaired':True,'scope_u8_repaired':True,'constructor_bindings_installed':True,'thread_new_absent_name_installed':True,'thread_physical_word_models_installed':True,'default_stack_helpers_installed_in_original_history':False,'concrete_Values_binding_discharged':False,'integrated_v2_source_adequacy_proved':False,'full_contracts_rebound':False,'nonvacuous_same_history_exports':False,'row_closures':[],'endpoint_premises_removed':[],'endpoint_premises_added':[],'T_changes':[],'next_lean':55148,'next_raw':55191,'runtime':'PV_LIB_SPEC_NativeMemory12','history':'PV_LIB_SPEC_MemoryHistory12.original'}
(L/'SESSION12_STATUS.json').write_text(json.dumps(status,indent=2)+'\n')
prov=[]
for rec in records:
 row={k:rec[k] for k in ['attempt','target','source_revision','source_sha256','accepted','exit','wall','peak_rss_kbytes','swaps','axioms_summary_based']}
 row['path']='lean/'+rec['target']+'.lean'
 if rec['accepted']:
  commit=subprocess.check_output(['git','log','-1','--diff-filter=A','--format=%H','--',row['path']],cwd=R,text=True).strip()
  b=subprocess.check_output(['git','show',commit+':'+row['path']],cwd=R)
  assert hashlib.sha256(b).hexdigest()==rec['source_sha256']
  row['passing_source_commit']=commit
 prov.append(row)
(L/'SESSION12_PROVENANCE.json').write_text(json.dumps({'attempts':prov},indent=2)+'\n')
(L/'SESSION12_VALIDATION.json').write_text(json.dumps({'records':records},indent=2)+'\n')
mapdelta={'shared_map_edited':False,'full_contracts_rebound':False,'row_closures':[],'final_runtime':status['runtime'],'final_history':status['history'],'new_modules':mods,'slots':{'ScopeData4963':'C9 canonical AtomicBool u8 accepted; actual v2 load checked; original source binding OPEN','native123/455/456':'Constructor values installed; exact source tokens/callback capture rechecked; original reachability OPEN','native122/214':'Physical qword models and local count1->2; native Thread/TLS validity/source prefix OPEN','native213':'Absent-name48/8 allocation/sparse stores installed, retained r14 sourced from local4; Some-name and original prefix OPEN','callback13923':'C10 finite source/native frame resolver installed, local poll checked; original frame/hook branch OPEN','ThreadInit14756':'Original continuous history and nonvacuous exports OPEN','OwnInit':'Full joint witness and full negation OPEN'}}
(L/'SESSION12_MAP_DELTA.json').write_text(json.dumps(mapdelta,indent=2)+'\n')
(L/'SESSION12_COMMITS_BEFORE_FINAL.txt').write_text(subprocess.check_output(['git','log','--oneline',status['base_revision']+'..HEAD'],cwd=R,text=True))
print('Retained',len(accepted),'passing compiles,',len(failed),'changed-before-retry failures,',len(mods),'semantic modules')
