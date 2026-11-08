"""Derive source provenance/status from retained receipts; never replay Lean."""
from pathlib import Path
import json,hashlib,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
records=[];logical=[]
for a in range(55700,55781):
 r=json.loads((L/f'receipt-{a}.json').read_text());path='lean/'+r['target']+'.lean'
 raw=r['source_revision'];parent='528052a351c63911579a9d21cc6ccf662f110d78' if a==55733 else subprocess.check_output(['git','rev-parse',raw+'^{commit}'],cwd=R,text=True).strip()
 v={'attempt':a,'target':r['target'],'path':path,'source_sha256':r['source_sha256'],'accepted':r['accepted'],'class':r['class'],'source_parent_revision':parent,'raw_receipt_revision':raw}
 if r['accepted']:
  commits=subprocess.check_output(['git','log','--diff-filter=A','--format=%H','68795ef34cb..HEAD','--',path],cwd=R,text=True).splitlines()
  assert len(commits)==1,(a,path,commits)
  v['passing_source_commit']=commits[0]
  assert sha(subprocess.check_output(['git','show',commits[0]+':'+path],cwd=R))==r['source_sha256']
  if 'RawAudit' not in r['target']:logical.append(r['target'])
 records.append(v)
rawfile=L/'SESSION18_RAW_AUDIT.json';audit=json.loads(rawfile.read_text()) if rawfile.exists() else None
passed=bool(audit and audit['exit']==0 and audit['all_equal'] and audit['standard_axioms_only'] and audit['roots']==532)
provenance={'attempts':records,'receipt_revision_corrections':{'55733':'receipt-55733-CORRECTION.json'},'all_source_parents_canonicalized':True,'strict_audit_pending':not passed}
(L/'SESSION18_PROVENANCE.json').write_text(json.dumps(provenance,indent=2)+'\n')
s={'base_revision':'68795ef34cb758c72f9c544dd64bd581cc19fa68','full_task_complete':False,'orders_1_2_3_complete':True,'eighteen_successor_statements_compiled':True,'universal_contracts_inhabited':False,'entry_rebase_performed':True,'entry_stack_grant_inhabited':True,'source_model_prefix_steps':85,'native_answers_consumed_at85':5,'values_prefix_no_writer_before85':True,'values_suffix_full_coverage_proved':False,'reached_8248_295_454_proved':False,'full_source_joint_witness_inhabited':False,'conditional_only_on_laneA_joins_proved':False,'full_joint_contradiction_proved':False,'new_findings':['SPEC-C16','SPEC-C17'],'repaired_existing_findings':['SPEC-C13 entry','SPEC-C14 successor statements'],'accepted_focused':[r['attempt'] for r in records if r['accepted']],'failed_focused':[r['attempt'] for r in records if not r['accepted'] and r['class']=='elaboration'],'admission_refusals':[r['attempt'] for r in records if r['class']=='admission'],'rows_closed':0,'endpoint_premises_added':False,'endpoint_premises_removed':False,'T_changes':False,'new_logical_modules':len(logical),'new_logical_roots':532,'strict_audit_attempt':55495,'stopped_audit_attempt':55494,'stopped_audit_earns_no_pass':True,'strict_audit_pending':not passed,'strict_audit_passed':passed,'next_lean':55781,'next_raw':55496,'native_target_module':'PV_LIB_SPEC_NativeTargets18','join_interface':'PV_LIB_SPEC_LaneAJoins18','current_entry_module':'PV_LIB_SPEC_EntryWorld18','contracts_module':'PV_LIB_SPEC_ContextFinalContracts18','preliminary_contracts_superseded':True,'receipt_revision_erratum':'receipt-55733-CORRECTION.json'}
(L/'SESSION18_STATUS.json').write_text(json.dumps(s,indent=2)+'\n')
print(json.dumps({'accepted':len(s['accepted_focused']),'elaboration_failures':len(s['failed_focused']),'admission_refusals':s['admission_refusals'],'logical_modules':len(logical),'final_strict_pass':passed}))
