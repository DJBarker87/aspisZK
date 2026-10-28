"""Source-association preflight. Never substitutes a full structural native law."""
from pathlib import Path
import json,lzma,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');O=D/'classify-root-gates';O.mkdir(exist_ok=True);plan=json.loads((D/'gate-plan.json').read_text());sources=json.loads(lzma.open(D/'classify-source-capture/sources.json.xz').read())['files'];cache={};result=[]
for r in plan:
 checks=[]
 for cohort,roots in r['roots'].items():
  for root in roots:
   v=root.get('source');p=root.get('project');entry=dict(cohort=cohort,function=root['function'],source_class=root['classification'])
   if v:
    key=v['key'];path=Path(sources[key]['path']);expected=v['file_sha256'];entry['path']=str(path)
   elif p:
    path=D/'src'/p['path'];expected=p['file_pin']['sha256'];entry['path']=str(path)
   else:entry['status']='UNRESOLVED SOURCE SPAN';checks.append(entry);continue
   if str(path) not in cache:cache[str(path)]=hashlib.sha256(path.read_bytes()).hexdigest()
   entry.update(file_sha256=cache[str(path)],expected_sha256=expected,status='PIN MATCH' if cache[str(path)]==expected else 'FINDING: SOURCE PIN DISAGREEMENT');checks.append(entry)
 result.append(dict(row=r['id'],checks=checks,root_shape='UNCHANGED SOURCE' if all(x['classification']=='A-function' for vs in r['roots'].values() for x in vs) else 'DIFFERENT/UNRESOLVED SOURCE',closure='Known reached-body source differences listed; remaining callbacks/macros unresolved. This preflight is not a complete structural gate.',changed_function_classes=[dict(function=x['function'],classification=x['classification']) for x in r['changed']]))
(O/'results.json').write_text(json.dumps(dict(results=result,definition='Read-only pin/source-association preflight, distinct from rerun original complete-body structural gates.'),indent=2)+'\n');assert not any(x['status'].startswith('FINDING') for r in result for x in r['checks']);print('41 row source-association preflights recorded; no native-law credit inferred')
