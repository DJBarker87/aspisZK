"""Summarize exact receipts and fresh-object declaration audits, without prover work."""
from pathlib import Path
import json,re,collections
E=Path(__file__).resolve().parent;p=json.loads((E/'RPz2_source-plan.json').read_text()); rows=[]
for f in sorted(E.glob('RPz2_*/receipt.json')):
 d=json.loads(f.read_text());d['receipt']=str(f.relative_to(E));d['audit_status']='printed' if d['print_axioms'] else 'not run (empty is not standard-only)';rows.append(d)
summary=dict(attempts=len(rows),passed=sum(r['exit_status']==0 for r in rows),failed=sum(r['exit_status']!=0 for r in rows),wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max([int(r['peak_rss_kib']) for r in rows]+[0]),swaps=sum(int(r['swaps']) for r in rows),source_plan_revision=p['revision'],targets=[{k:r.get(k) for k in ['attempt','module','repository_source','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','audit_status','print_axioms','receipt']} for r in rows])
(E/'RPz2_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
imports={};axs={};decls=[];complete=[];audited=set()
for f in sorted(E.glob('RPz2_*/stdout.log')):
 receipt=json.loads((f.parent/'receipt.json').read_text())
 if receipt['exit_status']!=0:continue
 for l in f.read_text().splitlines():
  for key in ['RPZ_IMPORTS','RPZ_AXIOM','RPZ_DECL']:
   if key+' ' in l:
    d=json.loads(l.split(key+' ',1)[1])
    if key=='RPZ_IMPORTS':imports[d['module']]=d['imports']
    elif key=='RPZ_AXIOM':axs[d['name']]=d['module']
    else:decls.append(d)
  if 'RPZ_AUDIT_COMPLETE ' in l:
   complete.append({'attempt':f.parent.name,'message':l})
   audited.update(receipt.get('audit_modules',[]))
standard={'propext','Classical.choice','Quot.sound'}
modules=collections.defaultdict(list)
for d in decls:modules[d['module']].append(d)
findings={}
for m in sorted(audited):
 ds=modules[m]
 closure=set();todo=[m]
 while todo:
  n=todo.pop()
  if n in closure:continue
  closure.add(n);todo.extend(imports.get(n,[]))
 findings[m]=dict(declarations=len(ds),declaration_nonstandard_axioms=sorted({a for d in ds for a in d['axioms'] if a not in standard}),import_closure_nonstandard_axioms=sorted(a for a,o in axs.items() if o in closure and a not in standard),closure_modules=len(closure),unknown_import_headers=sorted(n for n in closure if n not in imports))
state=json.loads((E/'RPz2_state.json').read_text())
passed={r['module'] for r in rows if r['exit_status']==0 and not r['module'].startswith('RPz2_Audit')}
audit=dict(scope='Only successfully replayed and explicitly audited repository modules; target Rc7_Top.deployed not inferred',completion_markers=complete,modules=findings,successful_replay_modules=len(passed),audit_missing_successful_replay_modules=sorted(passed-audited),nonstandard_axiom_owners={a:o for a,o in axs.items() if a not in standard},declarations=decls)
(E/'RPz2_axiom-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print({k:v for k,v in summary.items() if k!='targets'});print('audited modules',len(findings),'decls',len(decls),'missing',len(passed-audited))
