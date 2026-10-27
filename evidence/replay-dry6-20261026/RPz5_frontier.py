"""Classify the exact committed-source frontier without invoking Lean."""
from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent
p=json.loads((E/'RPz5_source-plan.json').read_text());s=json.loads((E/'RPz5_state.json').read_text())['state']
passed={m for m in p['order'] if s.get(m)=='passed'};failed={m for m in p['order'] if s.get(m)=='failed'};bad=set(failed)
for m in p['order']:
 if any(n in bad for n in p['modules'][m]['imports']):bad.add(m)
blocked=bad-failed;unattempted=set(p['order'])-passed-failed-blocked
ready={m for m in unattempted if all(p['modules'][n]['kind']=='trusted-library' or n in passed for n in p['modules'][m]['imports'])}
assert not (passed&bad)
counts={'repository_modules':len(p['order']),'green_contexts':len(passed),'failed_vertices':len(failed),'blocked_descendants':len(blocked),'other_unattempted':len(unattempted),'ready_unattempted':len(ready),'unresolved_names':len(p['unresolved'])}
assert sum(counts[k] for k in ['green_contexts','failed_vertices','blocked_descendants','other_unattempted'])==len(p['order'])
def closure(root):
 seen=set();todo=[root]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(p['modules'][n].get('imports',[]))
 return sum(p['modules'][n]['kind']=='repository' for n in seen)
out={'scope_counts':{'Rc10_Top':closure('Rc10_Top'),'Rc7_Top':closure('Rc7_Top'),'requested_union':len(p['order'])},'counts':counts,'failed':sorted(failed),'blocked_descendants':sorted(blocked),'other_unattempted':sorted(unattempted),'ready':sorted(ready),'top_state':{m:s.get(m,'blocked' if m in blocked else 'unattempted') for m in ['Rc7_Top','Rc8_Top','Rc9_Top','Rc10_Top']},'qualification':'Current selected smaller source cohort only. Obsolete larger-cohort probe failures are retained separately, not merged into this state.'}
(E/'RPz5_frontier.json').write_text(json.dumps(out,indent=2)+'\n')
print(counts);print('failed',out['failed']);print('tops',out['top_state'])
