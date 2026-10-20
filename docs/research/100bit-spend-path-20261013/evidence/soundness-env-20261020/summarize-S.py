"""Read receipts only; no build or replay."""
import json,collections,hashlib,re
from pathlib import Path
D=Path(__file__).resolve().parent
man=json.loads((D/'manifest-S.json').read_text());mods={e['module']:e for e in man['order']}
records=[json.loads(l) for l in (D/'status.jsonl').read_text().splitlines()];by={r['module']:r for r in records}
attempts=[json.loads(l) for l in (D/'attempts.jsonl').read_text().splitlines()]
for r in attempts:r['source_revision']=man['repo_revision']
(D/'attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in attempts))
audits=[json.loads(l) for l in (D/'axioms-batches.jsonl').read_text().splitlines()]
# Reparse full raw audit output, including wrapped axiom lists. No compiler rerun.
for r in audits:
 p=D/f"out-{r['attempt']}.log"
 if not p.exists():continue
 reports=list(re.finditer(r'^S_AXIOMS ([^\n|]+) \| ([^\n|]+) \| (\[[^\]]*\])',p.read_text(),re.M))
 counts={m:0 for m in r['modules']};nonstandard=[]
 for match in reports:
  owner,decl,ax=match.groups();counts[owner]+=1
  axs=[re.sub(r'\s+',' ',a).strip() for a in ax.strip('[]').split(',') if a.strip()]
  if set(axs)-{'propext','Classical.choice','Quot.sound'}:nonstandard.append({'module':owner,'declaration':decl,'axioms':axs})
 r.update(declaration_counts=counts,nonstandard=nonstandard,axiom_reports=len(reports),axiom_parser='multiline bracket-delimited; reparsed retained output')
(D/'axioms-batches.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in audits))
audited={m for r in audits if r['exit']==0 for m in r['modules']}
current={m for m,r in by.items() if r['status'].startswith('current')}
(D/'current-objects.json').write_text(json.dumps([{'module':m,'source_sha256':mods[m]['sha256'],'object_sha256':by[m]['object_sha256'],'status':by[m]['status']} for m in sorted(current)],indent=2)+'\n')
nonstandard=[x for r in audits if r['exit']==0 for x in r['nonstandard']]
nsmods=sorted({x['module'] for x in nonstandard})
formatter=[x for x in nonstandard if any('Formatter' in a for a in x['axioms'])]
other=[x for x in nonstandard if any(a not in {'propext','Classical.choice','Quot.sound'} and 'Formatter' not in a for a in x['axioms'])]
audit_summary={'method':'Lean.collectAxioms: same API as #print axioms; all declarations owned by current source modules, including definitions and opaque types','current_modules':len(current),'audited_current_modules':len(current&audited),'unaudited_current_modules':sorted(current-audited),'declarations_audited':sum(sum(r['declaration_counts'].values()) for r in audits if r['exit']==0),'standard_only_modules':sorted(current&audited-set(nsmods)),'nonstandard_modules':nsmods,'formatter_dependent_modules':sorted({x['module'] for x in formatter}),'formatter_declarations':formatter,'other_nonstandard_declarations':other,'failed_audit_attempts':[r for r in audits if r['exit']!=0]}
(D/'axioms-audit.json').write_text(json.dumps(audit_summary,indent=2)+'\n')
audit_for={m:r for r in audits if r['exit']==0 for m in r['modules']}
for r in attempts:
 r['resource_limits']={'lean_memory_mb':7000,'MemoryHigh':'6G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':64,'lean_threads':1}
 ar=audit_for.get(r['module'])
 r['axioms_audit']={'attempt':ar['attempt'],'declarations':ar['declaration_counts'][r['module']],'standard_only_owned_declarations':r['module'] not in nsmods} if ar else {'status':'not audited (failed, blocked, or budget exhausted)'}
(D/'attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in attempts))

def blockers(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return []
 seen.add(m)
 if m not in mods:return [{'module':m,'reason':'unresolved source or library'}]
 r=by.get(m)
 if r and r['status'].startswith('current'):return []
 if not r:return [{'module':m,'reason':'not reached'}]
 if r['status']=='failed':return [{'module':m,'reason':'compile failed','attempt':r['attempt'],'errors':r['errors']}]
 if r.get('blocked_imports'):return [b for d in r['blocked_imports'] for b in blockers(d,seen)]
 return [{'module':m,'reason':r.get('reason','skipped')}]
rootrows=[]
for m in man['roots']:
 r=by.get(m,{});rootrows.append({'module':m,'status':r.get('status','not reached'),'attempt':r.get('attempt',r.get('reused_receipt',{}).get('attempt')),'axioms_audited':m in audited,'owned_declarations_standard_only':m in audited and m not in nsmods,'blockers':blockers(m)})
(D/'roots-current.json').write_text(json.dumps(rootrows,indent=2)+'\n')
# Exact named theorem findings, from successful audit output.
targets=['checked_acceptance_failure_bound_no_model','recorded_extractor_cost_and_failure','hchecks_partial','hchecks_deployed_partial'];findings={t:[] for t in targets}
for r in audits:
 if r['exit']!=0:continue
 p=D/f"out-{r['attempt']}.log"
 if not p.exists():continue
 for match in re.finditer(r'^S_AXIOMS ([^\n|]+) \| ([^\n|]+) \| (\[[^\]]*\])',p.read_text(),re.M):
  owner,decl,axs=match.groups();axs=re.sub(r'\s+',' ',axs)
  for t in targets:
   if decl.endswith('.'+t):findings[t].append({'module':owner,'declaration':decl,'axioms':axs,'audit_attempt':r['attempt']})
(D/'named-root-axioms.json').write_text(json.dumps(findings,indent=2)+'\n')
failed=[r for r in records if r['status']=='failed'];(D/'failed-modules.json').write_text(json.dumps(failed,indent=2)+'\n')
(D/'skipped-modules.json').write_text(json.dumps([r for r in records if r['status']=='skipped'],indent=2)+'\n')
counts=collections.Counter(r['status'] for r in records)
summary={'source_revision':man['repo_revision'],'branch':'codex/cx-soundness-env-20261020','manifest_modules':man['module_count'],'manifest_libraries':man['library_count'],'preflight_unresolved_imports':len(man['problems']),'source_conflicts':len(man['conflicts']),'counts':dict(counts),'current':len(current),'failed':len(failed),'skipped':counts['skipped'],'not_reached':len(mods)-len(by),'source_attempts':len(attempts),'audit_attempts':len(audits),'attempts_used':sorted(r['attempt'] for r in attempts+audits),'peak_rss_kib_this_job':max((r.get('peak_rss_kib',0) for r in attempts+audits),default=0),'process_swaps_this_job':sum(r.get('swaps',0) for r in attempts+audits),'driver_wall':json.loads((D/'driver-wall.json').read_text()) if (D/'driver-wall.json').exists() else None,'sum_attempt_wall_seconds_including_locks':sum(r.get('wall_seconds_including_lock',0) for r in attempts+audits),'audited_current_modules':len(current&audited),'formatter_dependent_modules':audit_summary['formatter_dependent_modules'],'other_nonstandard_declaration_count':len(other),'current_requested_roots':[r['module'] for r in rootrows if r['status'].startswith('current')],'blocked_requested_roots':[r['module'] for r in rootrows if not r['status'].startswith('current')],'axioms_audit_complete':current<=audited,'joint_import_compatible':False,'joint_import_failure_attempt':6975,'c2_closed':False,'note':'Full --require-complete preflight failed. No failed source module was retried. All counts distinguish retained coherent objects from fresh compiles.'}
import datetime
start=datetime.datetime.fromisoformat(records[0]['timestamp_utc']).timestamp()
end=max((D/f"out-{r['attempt']}.log").stat().st_mtime for r in attempts+audits if (D/f"out-{r['attempt']}.log").exists())
summary['job_wall_seconds_through_last_receipt']=end-start
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['counts','current','failed','skipped','not_reached','peak_rss_kib_this_job','process_swaps_this_job','source_attempts','audit_attempts','audited_current_modules']},indent=2))
