"""Summarize immutable receipts, preserving earlier history and source revisions."""
import json,collections,hashlib,re,datetime
from pathlib import Path
D=Path(__file__).resolve().parent
read=lambda n:json.loads((D/n).read_text())
lines=lambda n:list(map(json.loads,(D/n).read_text().splitlines())) if (D/n).exists() else []
man=read('manifest-S.json');mods={e['module']:e for e in man['order']};by=read('continuation-final-status.json');prior=read('continuation-prior-status.json')
attempts=lines('attempts.jsonl');new=[r for r in attempts if 7000<=r['attempt']<=7899];audits=lines('axioms-batches.jsonl')+lines('continuation-axioms-batches.jsonl');retained=set(read('continuation-retained-audits.json'))
current={m for m,r in by.items() if r['status'].startswith('current')}
usable=[r for r in audits if r['exit']==0 and (r['attempt']>=7900 or set(r['modules'])<=retained)]
audited={m for r in usable for m in r['modules']};ns=[d for r in usable for d in r['nonstandard']];nsmods={d['module'] for d in ns}
findings={t:[] for t in ['checked_acceptance_failure_bound_no_model','recorded_extractor_cost_and_failure','hchecks_partial','hchecks_deployed_partial']}
for r in usable:
 out=(D/f"out-{r['attempt']}.log").read_text()
 for match in re.finditer(r'^S_AXIOMS ([^\n|]+) \| ([^\n|]+) \| (\[[^\]]*\])',out,re.M):
  owner,decl,axs=match.groups()
  for t in findings:
   if decl.endswith('.'+t):findings[t].append({'module':owner,'declaration':decl,'axioms':re.sub(r'\s+',' ',axs),'audit_attempt':r['attempt']})
(D/'named-root-axioms.json').write_text(json.dumps(findings,indent=2)+'\n')
def closure(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return seen
 seen.add(m)
 if m in mods:
  for dep in mods[m]['imports']:closure(dep,seen)
 return seen
def blockers(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return []
 seen.add(m);r=by.get(m,{})
 if r.get('status','').startswith('current'):return []
 if r.get('blocked_imports'):return [b for dep in r['blocked_imports'] for b in blockers(dep,seen)]
 return [{'module':m,'status':r.get('status','missing'),'reason':r.get('reason','compile failed'),'attempt':r.get('attempt'),'errors':r.get('errors',[]),'import_closure_size':r.get('import_closure_size',len(closure(m))-1)}]
rows=[]
for m in man['roots']:
 r=by.get(m,{});c=closure(m);cs=current&c
 rows.append({'module':m,'status':r.get('status','missing'),'attempt':r.get('attempt',r.get('reused_receipt',{}).get('attempt')),'import_closure_size':len(c)-1,'axioms_audited':m in audited,'owned_declarations_standard_only':m in audited and m not in nsmods,'closure_current':c&set(mods)<=current,'current_closure_fully_audited':cs<=audited,'generated_collision_sides':sorted(c&{'Stage2ContinuationTypes','AspisR1PublicPreparation.Types'}),'additional_generated_collision_sides':sorted(c&{'AspisR1PublicSerializer.Types','AspisR1RecordParser.Types'}),'blockers':blockers(m)})
(D/'roots-current.json').write_text(json.dumps(rows,indent=2)+'\n')
(D/'root-status-table.md').write_text('| Root | Status | Attempt | Imports | Owned audit | Blockers |\n|---|---|---:|---:|---|---|\n'+''.join('| '+r['module']+' | '+r['status']+' | '+str(r['attempt'] or '')+' | '+str(r['import_closure_size'])+' | '+('standard' if r['owned_declarations_standard_only'] else 'nonstandard' if r['axioms_audited'] else 'unavailable')+' | '+', '.join(b['module'] for b in r['blockers'])+' |\n' for r in rows))
audit={'method':'Lean.collectAxioms (same API as #print axioms), every declaration owned by current source modules plus reachable retained CompPoly modules; immutable successful prior audits retained','current_modules':len(current),'audited_current_modules':len(current&audited),'unaudited_current_modules':sorted(current-audited),'standard_only_modules':sorted(current&audited-nsmods),'nonstandard_modules':sorted(nsmods),'formatter_dependent_modules':sorted({d['module'] for d in ns if any('Formatter' in a for a in d['axioms'])}),'nonstandard_declarations':ns,'declarations_audited':sum(r['axiom_reports'] for r in usable),'external_comppoly_modules_audited':sorted(m for m in audited if m.startswith('CompPoly.')),'failed_new_audit_attempts':[r for r in audits if r['attempt']>=7900 and r['exit']!=0]}
(D/'axioms-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
# Annotate all receipts with audit evidence, without changing their historical source revision.
audit_for={m:r for r in usable for m in r['modules']}
for r in attempts:
 ar=audit_for.get(r['module']) if r.get('exit')==0 else None;r['axioms_audit']={'attempt':ar['attempt'],'declarations':ar['declaration_counts'][r['module']],'standard_only_owned_declarations':r['module'] not in nsmods} if ar else {'status':'not audited (failed or blocked)'}
 if r['attempt']>=7000:r['resource_limits']={'lean_memory_mb':7000,'MemoryHigh':'6G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':64,'lean_threads':1}
(D/'attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in attempts))
failed=[r for r in by.values() if r['status']=='failed'];skipped=[r for r in by.values() if r['status']=='skipped'];counts=collections.Counter(r['status'] for r in by.values())
(D/'failed-modules.json').write_text(json.dumps(failed,indent=2)+'\n');(D/'skipped-modules.json').write_text(json.dumps(skipped,indent=2)+'\n')
metrics=new+lines('continuation-axioms-batches.jsonl')
summary={'source_revision':man['repo_revision'],'source_sha256s_in_manifest':True,'branch':'codex/cx-soundness-env2-20261020','manifest_modules':len(mods),'manifest_libraries':len(man['libraries']),'preflight_unresolved_imports':len(man['problems']),'counts':dict(counts),'current':len(current),'failed':len(failed),'skipped':len(skipped),'continuation_source_attempts':len(new),'continuation_audit_attempts':len(metrics)-len(new),'attempts_used_continuation':[r['attempt'] for r in metrics],'peak_rss_kib_continuation':max((r['peak_rss_kib'] for r in metrics),default=0),'swaps_continuation':sum(r['swaps'] for r in metrics),'sum_wall_seconds_including_locks':sum(r['wall_seconds_including_lock'] for r in metrics),'audited_current_modules':len(current&audited),'axioms_audit_complete':current<=audited,'formatter_dependent_modules':audit['formatter_dependent_modules'],'current_requested_roots':[r['module'] for r in rows if r['status'].startswith('current')],'blocked_requested_roots':[r['module'] for r in rows if not r['status'].startswith('current')],'current_bin_roots':sum(r['module'].startswith('Bin') and r['status'].startswith('current') for r in rows),'collision_roots':read('collision-closures.json')['roots'],'joint_union_import_compatible':False,'joint_import_failure_attempt':6975,'c2_closed':False,'memory_failures':[{'module':r['module'],'attempt':r['attempt'],'import_closure_size':r['import_closure_size'],'errors':r['errors']} for r in failed if any('memory' in e.lower() for e in r['errors'])]}
summary['source_attempt_wall_seconds_including_locks']=sum(r['wall_seconds_including_lock'] for r in new)
summary['continuation_wall_seconds_through_last_receipt']=max((D/f"out-{r['attempt']}.log").stat().st_mtime for r in metrics)-min(datetime.datetime.fromisoformat(r['timestamp_utc']).timestamp()-r['wall_seconds_including_lock'] for r in lines('continuation-status.jsonl') if 'attempt' in r)
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
