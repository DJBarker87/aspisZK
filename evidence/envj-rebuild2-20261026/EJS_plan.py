"""Read-only resume plan from retained canonical journal and source manifest."""
from pathlib import Path
import json,subprocess,shlex,collections
O=Path(__file__).parent
remote='''from pathlib import Path
import json
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
def lines(n):return [json.loads(l) for l in (T/n).read_text().splitlines() if l.strip()]
print(json.dumps(dict(attempts=lines('EJR_attempts.jsonl'),reuses=lines('EJR_reuses.jsonl'),sources=json.loads((T/'EJR_all-restored-sources.json').read_text()),progress=json.loads((T/'EJR_progress.json').read_text()))))
'''
d=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(remote)],text=True))
old=json.loads((O.parent/'envj-rebuild-20261026/EJR_resume-plan.json').read_text())
a=d['attempts'];latest={r['key']:r for r in a};reused={r['key'] for r in d['reuses']}
unattempted=[r for r in d['sources'] if r['workspace']+':'+r['module'] not in latest and r['workspace']+':'+r['module'] not in reused]
fail=[r for k,r in latest.items() if r['exit'] and k not in reused]
plan=dict(next_attempt=30000+len(a),cumulative_attempts=len(a),additional_budget_used=len(a)-800,additional_budget_remaining=1600-len(a),allowed_attempt_range=[30800,34999],cumulative_limit=1600,unattempted_sources=unattempted,latest_failed=fail,canonical_progress=d['progress'],excluded_modules=['R1Z/EventsR1P2','R1Z/SimCostOuterRetry6'],no_unchanged_resource_retry=True,profile_followups=['CertBuildExtracted d7e06b9f7a29e903f7cf24c2305b80b91658dc8a86ae6aaaecca8a815f26a776 and dependent chain before CertOwnFill','Explicit repaired Formatter profile then two SamplerWordRead consumers; historical selected receipt was nonstandard'],status='Building' if len(a)<1600 else 'Budget exhausted; no further compile authorized')
for k,v in old.items():
 if 'unresolved' in k:plan[k]=v
(O/'EJS_resume-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps({k:v for k,v in plan.items() if k in ['next_attempt','cumulative_attempts','additional_budget_used','additional_budget_remaining','status']}));print('unattempted',len(unattempted),'latest failed',len(fail))
