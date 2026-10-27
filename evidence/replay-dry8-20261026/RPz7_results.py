"""Recount actual compiled contexts and audited declarations without Lean runs."""
from pathlib import Path
import json,re,collections,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
read=lambda p:json.loads(p.read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
p=read(E/'RPz7_plan.json');original=read(R/'evidence/replay-dry6-20261026/RPz5_source-plan.json');union=read(R/'evidence/replay-dry6-20261026/RPz5_tx1-probe-source-plan.json')
receipts=sorted([read(f) for f in E.glob('RPz7_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]))
reverse={r['module']:r['original'] for r in p['rows']};state={m:'passed' for m in p['reuse']}
for d in receipts:
 if d['module'] in reverse:state[reverse[d['module']]]='passed' if d['exit_status']==0 else 'failed'
mods=original['modules'];green=[m for m in original['order'] if state.get(m)=='passed'];failed=[m for m in original['order'] if state.get(m)=='failed'];remaining=[m for m in original['order'] if m not in state]
ready=[m for m in remaining if all(mods[n]['kind']=='trusted-library' or state.get(n)=='passed' for n in mods[m]['imports'])]
roots=[]
for root in ['Rc7_Top','Rc8_Top','Rc9_Top','Rc10_Top']:
 a=set()
 def visit(m):
  if m in a:return
  a.add(m)
  for n in mods[m].get('imports',[]):visit(n)
 visit(root);repo=[m for m in a if mods[m]['kind']=='repository']
 roots.append({'root':root,'repository_modules':len(repo),'green':sum(state.get(m)=='passed' for m in repo),'failed':sum(state.get(m)=='failed' for m in repo),'unbuilt':sum(m not in state for m in repo)})
frontier={'repository_modules':len(original['order']),'valid_reused':len(p['reuse']),'new_original_contexts':len(green)-len(p['reuse']),'green_contexts':len(green),'failed_vertices':failed,'unbuilt_count':len(remaining),'ready_count':len(ready),'dependency_blocked_unbuilt_count':len(remaining)-len(ready),'ready':ready,'remaining_original_modules':remaining,'remaining_prefixed_modules':[p['mapping'][m] for m in remaining],'roots':roots,'unresolved_names':0,'qualification':'Counts exclude the extra transport, inspection and audit modules. Unbuilt dependencies are a budget frontier, not failed proofs.'}
(E/'RPz7_frontier.json').write_text(json.dumps(frontier,indent=2)+'\n')
rows=[];headers={};import_conflicts=[];raw_count=0;groups=[];kernel_types=[];debug_refs=[];errors=[]
for d in receipts:
 if not d['module'].startswith('RPz7_Audit') or d['exit_status']!=0:continue
 log=(E/d['attempt']/'stdout.log').read_text();selected=set(d['deps_fingerprint']['selected_objects'])-{'Init','Lean'}
 groups.append({'attempt':d['attempt'],'modules':sorted(selected)});raw_count+=len(d['print_axioms'])
 if 'RPZ7_AUDIT_COMPLETE' not in log:errors.append({'missing_completion':d['attempt']})
 for line in log.splitlines():
  for tag in ['DECL','IMPORTS','KERNEL_TYPE','DEBUG_REF']:
   marker='RPZ7_'+tag+' '
   if marker not in line:continue
   try:x=json.loads(line.split(marker,1)[1])
   except Exception as exc:errors.append({'json_error':d['attempt'],'tag':tag,'error':str(exc)});continue
   if tag=='DECL':rows.append({**x,'audit_attempt':d['attempt'],'coverage_basis':'RPz7 fresh selected context'})
   elif tag=='IMPORTS':
    if x['module'] in headers and headers[x['module']]!=x['imports']:import_conflicts.append(x)
    headers[x['module']]=x['imports']
   elif tag=='KERNEL_TYPE':kernel_types.append(x)
   elif tag=='DEBUG_REF':debug_refs.append(x)
# Only unchanged source/dependency contexts reuse historical axiom evidence.
affected={'AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs'}
for m in original['order']:
 if any(n in affected for n in mods[m]['imports']):affected.add(m)
reaudit={m for m in p['reuse'] if m in affected};baseline=set(p['reuse'])-reaudit
old=read(R/'evidence/replay-dry6-20261026/RPz5_combined-audit.json')
inherited=[{**x,'coverage_basis':'unchanged historical context, source/object hashes rechecked'} for x in old['declarations'] if x['module'] in baseline]
combined=inherited+rows;standard={'propext','Classical.choice','Quot.sound'}
nonstandard=[r for r in combined if set(r['axioms'])-standard]
nonstd_axioms=sorted({a for r in nonstandard for a in r['axioms'] if a not in standard})
nonformatter=[r for r in nonstandard if 'CoreFmtDebug' not in r['name']]
expected_owners={d['module'] for d in receipts if d['exit_status']==0 and d['module'] not in ['RPz7_BeforeKernel'] and not d['module'].startswith('RPz7_Audit')}|reaudit
covered={m for g in groups for m in g['modules']};missing=sorted(expected_owners-covered)
for m in covered:
 expected=next((r['imports'] for r in p['rows'] if r['module']==m),None)
 if m=='RPz7_PhaseIso':expected=['Init','CurrentCompactFirstCompositionV1']
 elif m=='RPz7_PhaseConsumers':expected=['Init','RPz7_S1SemanticCodeVerifyV1','RPz7_S1SemanticCodeFinishV1']
 elif m in p['reuse']:expected=(union if p['reuse'][m]=='RPz5_union_overlay' else original)['modules'][m]['imports']
 if headers.get(m)!=expected:errors.append({'header_mismatch':m,'expected':expected,'actual':headers.get(m)})
counts=collections.Counter((r['module'],r['name']) for r in rows);dups=[{'module':m,'name':n,'count':c} for (m,n),c in counts.items() if c>1]
if raw_count!=len(rows):errors.append({'raw_structured_count_mismatch':[raw_count,len(rows)]})
if missing:errors.append({'missing_audits':missing})
if dups:errors.append({'duplicate_owner_name_queries':dups})
if import_conflicts:errors.append({'import_context_conflicts':import_conflicts})
audit={'groups':groups,'fresh_or_reaudited_contexts':len(covered),'inherited_unchanged_contexts':len(baseline),'fresh_declaration_queries':len(rows),'raw_print_results':raw_count,'inherited_declaration_queries':len(inherited),'combined_declaration_queries':len(combined),'nonstandard_queries':nonstandard,'nonstandard_axioms':nonstd_axioms,'nonformatter_nonstandard_queries':nonformatter,'all_declaration_standard_only_gate':not nonstandard,'missing_contexts':missing,'errors':errors,'declarations':combined,'kernel_type_records':kernel_types,'parser_formatter_direct_references':debug_refs,'fresh_top_axioms':None,'fresh_top_reachability':'UNKNOWN: fresh Rc10_Top not compiled'}
(E/'RPz7_axiom-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
current={(r['module'],r['name']):r for r in combined};formatter_records=[]
for r in old['nonstandard_queries']:
 now=current.get((r['module'],r['name']))
 formatter_records.append({**r,'selected_context_record_present':now is not None,'selected_context_axioms':now['axioms'] if now else None,'fresh_Rc10_reachable':None,'status':'UNKNOWN: no fresh top; partial-context audit cannot give top reachability'})
(E/'RPz7_formatter-records.json').write_text(json.dumps({'records':formatter_records,'records_count':len(formatter_records),'inherited_nonstandard_axioms':old['nonstandard_axioms'],'selected_context_nonstandard_axioms':nonstd_axioms,'fresh_top_available':False},indent=2)+'\n')
# Capture the exact historical cached type data without promoting it to a fresh top.
for d in receipts:
 if d['module']=='RPz7_BeforeKernel':
  log=(E/d['attempt']/'stdout.log').read_text();marker='RPZ7_KERNEL_STATEMENT '
  if d['exit_status']==0 and marker in log:
   line=next(line.split(marker,1)[1] for line in log.splitlines() if marker in line)
   statement=json.loads(line);raw=(json.dumps(statement,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode();(E/'RPz7_BEFORE.kernel.txt').write_bytes(raw)
   before_kernel={'attempt':d['attempt'],'sha256':sha(raw),'bytes':len(raw),'scope':'historical cached object, not a coherent fresh replay','representation':'canonical JSON of complete universe parameter-list repr and complete kernel-type Expr repr; no proof body'}
  else:before_kernel={'attempt':d['attempt'],'available':False,'exit_status':d['exit_status']}
  break
else:before_kernel={'available':False,'reason':'pinned historical root unavailable or changed; no substitute'}
ledger=read(E/'RPz7_statement-ledger.json');ledger['historical_before_kernel']=before_kernel;ledger['fresh_after_kernel']=None;ledger['fresh_kernel_statement_comparison']='NOT ESTABLISHED: budget exhausted before fresh top';ledger['frontier']=frontier;ledger['budget']={'lean_attempts':len(receipts),'limit':1498,'kani_runs':0};ledger['fresh_top_formatter_reachability']='UNKNOWN for every one of the 180 retained records';ledger['nonvacuity']='No fresh joint deployment witness. Checked Phase constructor witness and historical conditional deployment witnesses do not replace joint inhabitation.'
ledger.update({'new_attempts':len(receipts),'new_passed':sum(d['exit_status']==0 for d in receipts),'new_failed':sum(d['exit_status']!=0 for d in receipts),'lean_limit':1498,'kani_used':0,'kani_limit':0,'unused_lean_budget':1498-len(receipts),'stop_reason':'Round budget exhausted before fresh Rc7..Rc10; the old nominal equality gate is replaced by checked explicit transport','aggregate_compiler_wall_seconds':sum(d['wall_seconds'] for d in receipts),'peak_rss_kib':max(int(d['peak_rss_kib']) for d in receipts),'swaps':sum(int(d['swaps']) for d in receipts),'inherited_evidence':'RPz7_inherited-evidence-pins.json; source/cohort qualifications preserved','formatter_audit':{'historical_records':180,'selected_nonstandard_axioms':len(nonstd_axioms),'fresh_top_available':False,'fresh_top_reachability':'UNKNOWN per record'},'new_top_theorem':None,'phase_consumer_transport_checked':any(d['module']=='RPz7_PhaseConsumers' and d['exit_status']==0 for d in receipts),'all_selected_sources_rechecked':'See RPz7_final-verification.json for separate planning/reused/compiler-snapshot checks','source_hash_mismatches':'See RPz7_final-verification.json','shipped_source_changes':False,'elf_rebuild_triggered':False})
if not ledger['phase_consumer_transport_checked']:ledger['nonvacuity']='No fresh joint deployment witness; concrete Phase witness check failed or did not run.'
(E/'RPz7_statement-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
print('FRONTIER',len(green),'green',len(failed),'failed',len(remaining),'unbuilt',len(ready),'ready')
print('AUDIT',len(rows),'fresh queries',raw_count,'raw',len(nonstandard),'nonstandard records',len(nonstd_axioms),'nonstandard axioms',len(nonformatter),'nonformatter',len(errors),'errors')
assert not errors,errors
