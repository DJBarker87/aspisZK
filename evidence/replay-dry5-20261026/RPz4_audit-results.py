"""Parse structured kernel audit results; preserve raw printed axiom evidence."""
from pathlib import Path
import json,re,collections
E=Path(__file__).resolve().parent;g=json.loads((E/'RPz4_source-plan.json').read_text());s=json.loads((E/'RPz4_state.json').read_text())['state'];decl=[];refs=[];headers={};axs=[];groups=[];errors=[];rawprints=0
for f in sorted(E.glob('RPz4_*/receipt.json')):
 r=json.loads(f.read_text())
 if not r['module'].startswith('RPz4_Audit'):continue
 text=(f.parent/'stdout.log').read_text();cfg=json.loads((E/(r['attempt']+'.json')).read_text());ds=[];complete=[]
 for line in text.splitlines():
  hit=re.search(r'RPZ4_(DECL|DEBUG_REF|IMPORTS|AXIOM) (\{.*\})$',line)
  if hit:
   k=hit[1];v=json.loads(hit[2]);v['audit_attempt']=r['attempt']
   if k=='DECL':decl.append(v);ds.append(v)
   elif k=='DEBUG_REF':refs.append(v)
   elif k=='IMPORTS':headers[v['module']]=v['imports']
   else:axs.append(v)
  hit=re.search(r'RPZ4_AUDIT_COMPLETE declarations=(\d+) modules=(\d+)',line)
  if hit:complete.append([int(hit[1]),int(hit[2])])
 prints=sum('depends on axioms:' in l or 'does not depend on any axioms' in l for l in text.splitlines());rawprints+=prints
 group={'attempt':r['attempt'],'modules':cfg['audit_modules'],'exit_status':r['exit_status'],'structured_queries':len(ds),'raw_print_results':prints,'complete_markers':complete};groups.append(group)
 if r['exit_status']==0 and (complete!=[[len(ds),len(cfg['audit_modules'])]] or prints!=len(ds)):errors.append(group)
std={'propext','Classical.choice','Quot.sound'};bad=[d for d in decl if set(d['axioms'])-std];prefixes=['AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug','AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug'];external=[r for r in refs if not any(r['name']==p or r['name'].startswith(p+'.') for p in prefixes)];covered={m for x in groups if x['exit_status']==0 for m in x['modules']};passed={m for m in g['order'] if s.get(m)=='passed'};mismatches=[]
for m in sorted(covered):
 if m not in headers:mismatches.append({'module':m,'missing_header':True})
 elif set(headers[m])!=set(g['modules'][m]['imports']):mismatches.append({'module':m,'parsed':g['modules'][m]['imports'],'actual':headers[m]})
out={'audit_groups':groups,'declaration_queries':len(decl),'distinct_global_names':len({d['name'] for d in decl}),'duplicate_owner_name_pairs':[list(k) for k,n in collections.Counter((d['module'],d['name']) for d in decl).items() if n>1],'repeated_global_names':{k:n for k,n in collections.Counter(d['name'] for d in decl).items() if n>1},'declarations':decl,'raw_print_results':rawprints,'covered_modules':sorted(covered),'passed_modules_missing_audit':sorted(passed-covered),'source_import_header_mismatches':mismatches,'audit_completion_errors':errors,'nonstandard_queries':bad,'nonstandard_modules':dict(collections.Counter(d['module'] for d in bad)),'nonstandard_axioms':sorted({a for d in bad for a in d['axioms'] if a not in std}),'parser_formatter_direct_references':refs,'parser_formatter_external_consumers':external,'imported_axioms':axs,'standard_axiom_gate_for_all_audited_declarations':not bad,'formatter_scope_qualification':'No external consumer means no direct type/body reference outside the two formatter families among audited selected declarations. Missing sources and blocked modules are not elaborated; whole-top reachability is unknown until fresh Rc7_Top compiles.','fresh_top_reachability':'NOT REACHED' if s.get('Rc7_Top')!='passed' else 'See explicit fresh top declaration axiom record'}
(E/'RPz4_axiom-audit.json').write_text(json.dumps(out,indent=2)+'\n');print({k:out[k] for k in ['declaration_queries','raw_print_results','nonstandard_modules','nonstandard_axioms','parser_formatter_external_consumers','audit_completion_errors','source_import_header_mismatches','passed_modules_missing_audit']})
