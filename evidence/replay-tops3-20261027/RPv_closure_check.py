from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'RPv_plan.json').read_text());errors=[]
for root in p['roots']:
 receipts=[json.loads(f.read_text()) for f in E.glob('RPv_*/receipt.json')]
 d=next((d for d in receipts if d['module']=='RPv_'+root+'Audit' and d['exit_status']==0),None)
 if d is None:continue
 log=(E/d['attempt']/'stdout.log').read_text();headers={}
 for l in log.splitlines():
  if 'RPV_IMPORTS ' in l:
   x=json.loads(l.split('RPV_IMPORTS ',1)[1]);headers[x['module']]=x['imports']
 seen=set()
 def go(n):
  if n in seen:return
  seen.add(n)
  assert n in headers,('missing header',root,n)
  for m in headers[n]:go(m)
 go(p['mapping'][root])
 repo=set(p['mapping'].values());expected={p['mapping'].get(n,n) for n in p['closures'][root]};actual=seen&repo
 out={'target':p['mapping'][root],'attempt':d['attempt'],'planning_repository_contexts':len(p['closures'][root]),'planned_distinct_selected_module_names':len(expected),'checked_header_repository_contexts':len(actual),'planned_not_in_header':sorted(expected-seen),'additional_repository_header_contexts':sorted(actual-expected),'all_root_header_contexts_including_libraries':len(seen),'audit_environment_header_contexts_including_libraries':len(headers),'qualification':'Traversal starts at the actual checked top import header; audit-only imports do not inflate closure credit. Historical support-context classification follows the pinned predecessor.'}
 (E/f'RPv_{root}-import-closure-check.json').write_text(json.dumps(out,indent=2)+'\n')
 if out['planned_not_in_header'] or out['additional_repository_header_contexts']:errors.append(out)
 print(root,len(expected),len(actual),'missing',len(expected-seen),'extra',len(actual-expected))
assert not errors,errors
