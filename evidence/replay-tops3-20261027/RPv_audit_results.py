from pathlib import Path
import json
E=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
plan=read(E/'RPv_plan.json');wanted={r['module'] for r in plan['rows']};receipts=[read(f) for f in E.glob('RPv_*/receipt.json')];passed={d['module'] for d in receipts if d['exit_status']==0 and d['module'] in wanted};covered=set();declarations=[];nonstandard=[];errors=[];standard={'propext','Classical.choice','Quot.sound'}
groups=read(E/'RPv_audit-groups.json')
for index,group in enumerate(groups):
 module=f'RPv_AuditBatch{index+1:02d}';d=next((d for d in receipts if d['module']==module),None)
 if not d or d['exit_status']!=0:errors.append({'missing_or_failed_batch':module});continue
 log=(E/d['attempt']/'stdout.log').read_text();headers=[];decls=[]
 for l in log.splitlines():
  if 'RPV_IMPORTS ' in l:headers.append(json.loads(l.split('RPV_IMPORTS ',1)[1]))
  if 'RPV_DECL ' in l:decls.append(json.loads(l.split('RPV_DECL ',1)[1]))
 actual={r['module'] for r in headers};missing=set(group)-actual
 if missing:errors.append({'batch':module,'missing_context_headers':sorted(missing)})
 if len(decls)!=len(d['print_axioms']):errors.append({'batch':module,'structured_raw_count_mismatch':[len(decls),len(d['print_axioms'])]})
 covered.update(actual);declarations.extend(decls)
 nonstandard.extend(r for r in decls if set(r['axioms'])-standard)
if nonstandard:errors.append({'nonstandard_axiom_queries':len(nonstandard)})
if passed-covered:errors.append({'unaudited_source_contexts':sorted(passed-covered)})
out={'fresh_source_contexts':len(passed),'audited_contexts':len(covered),'declaration_queries':len(declarations),'nonstandard':nonstandard,'errors':errors,'declarations':declarations,'qualification':'Only fresh source contexts; unchanged predecessor audits are reused after pin checks. Imported formatter axioms remain in the retained library corpus.'}
(E/'RPv_axiom-audit.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='declarations'});assert not errors
