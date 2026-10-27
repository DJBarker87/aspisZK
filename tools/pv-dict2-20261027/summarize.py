from pathlib import Path
import json,re
E=Path('evidence/pv-dict2-20261027');t=json.loads((E/'TALLY.json').read_text());rows=[];forbidden=[]
for a in t['attempts']:
 if not a.get('charged'):continue
 r=json.loads((E/(str(a['id'])+'.json')).read_text());rows.append({k:r[k] for k in ['attempt','module','source_revision','source_sha256','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
 if r['exit_status']==0:
  output=r.get('axiom_output','')
  matches=list(re.finditer(r"depends on axioms: \[(.*?)\]",output,re.S))
  assert len(matches)==output.count('depends on axioms:'),(a['id'],'unparsed axiom report')
  for match in matches:
   names=[x.strip() for x in match[1].split(',') if x.strip()]
   if set(names)-{'propext','Classical.choice','Quot.sound'}:forbidden.append(dict(attempt=a['id'],line=match[0]))

success=list(dict.fromkeys(r['module'] for r in rows if r['exit_status']==0));queue=json.loads((E/'recheck-queue.json').read_text());pending=[m for m in queue if m not in success];plan=json.loads((E/'closure-plan.json').read_text())
out=dict(lean_charged=t['lean_charged'],kani=0,successful_compiles=sum(r['exit_status']==0 for r in rows),failed_compiles=sum(r['exit_status']!=0 for r in rows),unlaunched_admissions=sum(not a.get('charged') for a in t['attempts']),requested_roots=plan['roots'],consumer_results={m:m in success for m in plan['consumers']},pending_rechecks=pending,nonstandard_axiom_reports=forbidden,receipts=rows)
(E/'recheck-summary.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['receipts','pending_rechecks','requested_roots']});print('pending',len(pending))
assert not forbidden
