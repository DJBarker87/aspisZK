"""Summarize the actual replay frontier and complete attempt receipts."""
from pathlib import Path
import json,collections,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];g=json.loads((E/'RPz3_source-plan.json').read_text());state=json.loads((E/'RPz3_state.json').read_text())['state'];rs=[json.loads(f.read_text()) for f in sorted(E.glob('RPz3_*/receipt.json'))];sources=[r for r in rs if not r['module'].startswith('RPz3_Audit')];audits=[r for r in rs if r['module'].startswith('RPz3_Audit')];ready=[];fail=[]
for m in g['order']:
 if state.get(m)=='failed':fail.append(m)
 if m not in state or state[m]=='blocked':
  state[m]='blocked'
  if all(g['modules'][n]['kind']=='trusted-library' or state.get(n)=='passed' for n in g['modules'][m]['imports']):ready.append(m)
q=collections.deque([['Rc7_Top']]);seen=set();paths={}
while q:
 path=q.popleft();m=path[-1]
 if m in seen:continue
 seen.add(m)
 if m in fail or m in g['unresolved']:paths[m]=path
 for n in g['modules'][m].get('imports',[]):q.append(path+[n])
errors=[];limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in rs:
 a=r['attempt']
 for f in ['receipt.json','stdout.log','time.log']:
  if not (E/a/f).is_file():errors.append(a+' missing '+f)
 if r['limits']!=limits:errors.append(a+' caps')
 if '-M7000' not in r['command'] or '-j1' not in r['command']:errors.append(a+' Lean flags')
 if r['module'].startswith('RPz3_Audit'):
  for f,v in r['source_hashes'].items():
   if hashlib.sha256((E/f).read_bytes()).hexdigest()!=v:errors.append(a+' audit source hash')
 elif list(r['source_hashes'].values())!=[hashlib.sha256((R/r['repository_source']).read_bytes()).hexdigest()]:errors.append(a+' source hash')
 if not (E/(a+'-reservation.json')).is_file():errors.append(a+' missing admission receipt')
ids=sorted(int(r['attempt'].split('_')[1]) for r in rs)
fullerrors=[{'attempt':r['attempt'],'module':r['module'],'exit_status':r['exit_status'],'errors':(E/r['attempt']/'stdout.log').read_text()} for r in rs if r['exit_status']!=0]
out={'source_revision':g['revision'],'target':g['target'],'repository_modules_selected':len(g['order']),'unresolved':g['unresolved'],'closure_size_qualification':'Partial lower bound: missing/ambiguous sources may add imports. Trusted library transitive closure excluded by owner scope.','state_counts':dict(collections.Counter(state[m] for m in g['order'])),'ready_unattempted':ready,'failed_vertices':fail,'blocker_paths_from_top':paths,'target_state':state.get('Rc7_Top'),'lean_attempts':len(rs),'lean_budget':1500,'kani_runs':0,'kani_budget':0,'source_attempts':len(sources),'source_passed':sum(r['exit_status']==0 for r in sources),'audit_attempts':len(audits),'audit_passed':sum(r['exit_status']==0 for r in audits),'all_attempt_numbers_contiguous':ids==list(range(1,len(rs)+1)),'wall_seconds_sum':sum(r['wall_seconds'] for r in rs),'max_peak_rss_kib':max((int(r['peak_rss_kib']) for r in rs),default=0),'swaps_sum':sum(int(r['swaps']) for r in rs),'failures':fullerrors,'repeated_targets':[m for m,n in collections.Counter(r['module'] for r in rs).items() if n>1],'unchanged_input_retries':[list(k) for k,n in collections.Counter((r['module'],tuple(sorted(r['source_hashes'].values())),json.dumps(r['deps_fingerprint'],sort_keys=True)) for r in rs).items() if n>1],'verification_errors':errors,'top_source_unchanged':g['modules']['Rc7_Top']['sha256']=='f471ed2a3eaa6ba76d483fa9201a0f33df5b1cd6d732ef3d4335fd9dd716d38e','ledger_delta':{'T':0,'P':0,'G':0,'C':0},'premises_removed_added_changed':[0,0,0],'non_vacuity':'No fresh joint witness; historical conditional witnesses retained without strengthening.','top_axioms':'NOT REACHED; no historical top object substituted','top_FunsExternal_reachability':'UNKNOWN until fresh top compiles'}
(E/'RPz3_frontier.json').write_text(json.dumps(out,indent=2)+'\n');print({k:out[k] for k in ['repository_modules_selected','state_counts','ready_unattempted','lean_attempts','source_passed','audit_attempts','max_peak_rss_kib','verification_errors']})
