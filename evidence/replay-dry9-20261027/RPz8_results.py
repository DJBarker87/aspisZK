"""Exact replay frontier, failure descendants, root statement and formatter receipts."""
from pathlib import Path
import json,hashlib,collections
E=Path(__file__).resolve().parent;R=E.parents[1]
read=lambda p:json.loads(p.read_text())
base=read(R/'evidence/replay-dry6-20261026/RPz5_source-plan.json');old=read(R/'evidence/replay-dry8-20261026/RPz7_frontier.json');p=read(E/'RPz8_plan.json');arx=read(E/'RPz8_ARX-plan.json');plans=p['rows']+arx['rows'];lookup={r['module']:r for r in plans};originals={r['original']:r for r in plans};modules={m:x.get('imports',[]) for m,x in base['modules'].items()};modules.update({r['original']:[next((x['original'] for x in plans if x['module']==n),n) for n in r['imports']] for r in arx['rows']})
# ARX imports RPz7-prefixed selected contexts: invert the inherited mapping.
p7=read(R/'evidence/replay-dry8-20261026/RPz7_plan.json');reverse={v:k for k,v in p7['mapping'].items()};reverse.update({r['module']:r['original'] for r in plans})
for r in arx['rows']:modules[r['original']]=[reverse.get(n,n) for n in r['imports']]
rs=sorted([read(f) for f in E.glob('RPz8_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]));state={m:'passed' for m in base['order'] if m not in old['remaining_original_modules']};failures=[]
for d in rs:
 if d['module'] in lookup:state[lookup[d['module']]['original']]='passed' if d['exit_status']==0 else 'failed'
children=collections.defaultdict(list)
for m,im in modules.items():
 for n in im:children[n].append(m)
for d in rs:
 if d['exit_status']==0:continue
 m=lookup[d['module']]['original'] if d['module'] in lookup else d['module'];desc=set();stack=list(children[m])
 while stack:
  n=stack.pop()
  if n not in desc:desc.add(n);stack.extend(children[n])
 failures.append({'attempt':d['attempt'],'module':m,'exit_status':d['exit_status'],'full_stdout':(E/d['attempt']/'stdout.log').read_text(),'blocked_descendants':sorted(n for n in desc if state.get(n)!='passed')})
def closure(root):
 seen=set();todo=[root]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(modules.get(n,[]))
 return seen
alloriginal=list(base['order'])+arx['order'];roots=[]
for root in ['Rc7_Top','Rc8_Top','Rc9_Top','Rc10_Top','ARX_Root']:
 selected=[m for m in closure(root) if m in alloriginal];roots.append({'root':root,'repository_modules':len(selected),'green':sum(state.get(m)=='passed' for m in selected),'failed':sum(state.get(m)=='failed' for m in selected),'unbuilt':sum(m not in state for m in selected)})
remaining=[m for m in alloriginal if m not in state];ready=[m for m in remaining if all(n not in alloriginal or state.get(n)=='passed' for n in modules[m])]
frontier={'original_union_modules':len(base['order']),'ARX_additional_modules':len(arx['order']),'combined_modules':len(alloriginal),'inherited_green':old['green_contexts'],'new_green':sum(d['exit_status']==0 and d['module'] in lookup for d in rs),'green_contexts':sum(state.get(m)=='passed' for m in alloriginal),'failed_vertices':[m for m in alloriginal if state.get(m)=='failed'],'unbuilt_count':len(remaining),'remaining_original_modules':remaining,'ready':ready,'ready_count':len(ready),'dependency_blocked_unbuilt_count':len(remaining)-len(ready),'unresolved_names':0,'roots':roots,'lean_attempts':len(rs),'lean_limit':1500,'kani_runs':0,'compiler_wall_seconds':sum(d['wall_seconds'] for d in rs),'peak_rss_kib':max([int(d['peak_rss_kib']) for d in rs] or [0]),'swaps':sum(int(d['swaps']) for d in rs)}
(E/'RPz8_frontier.json').write_text(json.dumps(frontier,indent=2)+'\n');(E/'RPz8_failures.json').write_text(json.dumps(failures,indent=2)+'\n')
standard={'propext','Classical.choice','Quot.sound'};declarations=[];headers={};errors=[];rootaudits={}
for d in rs:
 log=(E/d['attempt']/'stdout.log').read_text()
 if d['exit_status']!=0:continue
 if d['module'] in ['RPz8_Rc10_TopAudit','RPz8_ARX_RootAudit']:
  name=d['module'].removeprefix('RPz8_').removesuffix('Audit');statement=None;formatters=[];rootimports={};reachable=[]
  for line in log.splitlines():
   for marker,kind in [('RPZ8_KERNEL_STATEMENT ','statement'),('RPZ8_FORMATTER ','formatter'),('RPZ8_IMPORTS ','imports'),('RPZ8_REACHABLE_CONSTANTS ','reachable')]:
    if marker not in line:continue
    x=json.loads(line.split(marker,1)[1])
    if kind=='statement':statement=x
    elif kind=='formatter':formatters.append(x)
    elif kind=='imports':rootimports[x['module']]=x['imports']
    else:reachable=x
  if statement is None or 'RPZ8_ROOT_AUDIT_COMPLETE' not in log:errors.append({'incomplete_root_audit':d['attempt']});continue
  raw=(json.dumps(statement,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode();(E/('RPz8_'+name+'.kernel.txt')).write_bytes(raw)
  # Import-path witnesses are additional to constant-level proof dependencies.
  def importpath(target):
   queue=[['RPz8_'+name]];seen=set()
   for path in queue:
    n=path[-1]
    if n==target:return path
    if n in seen:continue
    seen.add(n);queue.extend(path+[k] for k in rootimports.get(n,[]) if k not in seen)
   return []
  historical=read(R/'evidence/replay-dry8-20261026/RPz7_formatter-records.json')['records'];byname={r['name']:r for r in formatters};records=[]
  for oldr in historical:
   x=byname.get(oldr['name'])
   if x is None:errors.append({'missing_formatter_result':oldr['name'],'root':name});continue
   assert isinstance(x['reachable'],bool)
   records.append({**{k:v for k,v in oldr.items() if k!='fresh_Rc10_reachable'},**({'fresh_Rc10_reachable':x['reachable']} if name=='Rc10_Top' else {}),'fresh_root':name,'reachable':x['reachable'],'present_in_fresh_environment':x['present'],'constant_path':x['constant_path'],'constant_owner_path':x['owner_path'],'import_path':importpath(oldr['module']) if x['reachable'] else [],'status':'reachable' if x['reachable'] else 'not reachable','evidence_attempt':d['attempt']})
  result={'root':name,'attempt':d['attempt'],'kernel_statement_sha256':hashlib.sha256(raw).hexdigest(),'kernel_statement_bytes':len(raw),'print_axioms':d['print_axioms'],'reachable_constants':len(reachable),'formatter_count':len(records),'axiom_name_metadata_basis':'Inherited cached name lists; actual kernel classification is RPz8_formatter-axiom-reachability.json', 'reachable_formatters':sum(r['reachable'] for r in records),'records':records,'complete':len(records)==180}
  (E/('RPz8_'+name+'-formatter-records.json')).write_text(json.dumps(result,indent=2)+'\n');rootaudits[name]={k:v for k,v in result.items() if k!='records'}
  (E/('RPz8_'+name+'-reachable-constants.json')).write_text(json.dumps(reachable,indent=2)+'\n')
 if d['module'].startswith('RPz8_AuditBatch'):
  count=0
  for line in log.splitlines():
   if 'RPZ8_DECL ' in line:declarations.append({**json.loads(line.split('RPZ8_DECL ',1)[1]),'attempt':d['attempt']});count+=1
   if 'RPZ8_IMPORTS ' in line:
    x=json.loads(line.split('RPZ8_IMPORTS ',1)[1]);headers[x['module']]=list(dict.fromkeys(x['imports']))
  if count!=len(d['print_axioms']) or 'RPZ8_AUDIT_COMPLETE' not in log:errors.append({'audit_incomplete':d['attempt']})
for m,imports in headers.items():
 if imports!=list(dict.fromkeys(lookup[m]['imports'])):errors.append({'import_header_mismatch':m,'actual':imports,'expected':lookup[m]['imports']})
nonstandard=[r for r in declarations if set(r['axioms'])-standard]
covered=set(headers);passed={d['module'] for d in rs if d['exit_status']==0 and d['module'] in lookup}
audit={'roots':rootaudits,'fresh_audited_contexts':len(covered),'declaration_queries':len(declarations),'nonstandard_queries':nonstandard,'unaudited_passed_contexts':sorted(passed-covered),'errors':errors,'declarations':declarations,'qualification':'Unchanged inherited contexts reuse RPz7 audits after object hashes rechecked; no new compile credit.'};(E/'RPz8_axiom-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps({**{k:v for k,v in frontier.items() if k not in ['remaining_original_modules','ready']},'audited':len(covered),'nonstandard_new_queries':len(nonstandard),'audit_errors':errors,'roots_audited':rootaudits},indent=2))
