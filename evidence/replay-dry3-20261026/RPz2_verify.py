"""Final receipt consistency evidence, not a compiler/test invocation."""
from pathlib import Path
import json,hashlib,collections,subprocess
E=Path(__file__).resolve().parent;g=json.loads((E/'RPz2_source-plan.json').read_text());a=json.loads((E/'RPz2_axiom-audit.json').read_text());rs=[json.loads(f.read_text()) for f in sorted(E.glob('RPz2_*/receipt.json'))];errors=[];limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in rs:
 n=r['attempt'];p=E/n
 for f in ['stdout.log','time.log','receipt.json']:
  if not (p/f).is_file():errors.append(n+' missing '+f)
 for f in [n+'.json',n+'-reservation.json',n+'-launcher.log']:
  if not (E/f).is_file():errors.append(n+' missing '+f)
 if r['limits']!=limits:errors.append(n+' bad limits')
 if '-M7000' not in r['command'] or '-j1' not in r['command']:errors.append(n+' bad Lean arguments')
 if r['module'].startswith('RPz2_Audit'):
  for src,sha in r['source_hashes'].items():
   if hashlib.sha256((E/src).read_bytes()).hexdigest()!=sha:errors.append(n+' audit source mismatch')
 else:
  if list(r['source_hashes'].values())!=[g['modules'][r['module']]['sha256']]:errors.append(n+' repository source mismatch')
ids=[r['attempt'] for r in rs];numbers=[int(n.split('_')[1]) for n in ids];dup_targets=[n for n,c in collections.Counter(r['module'] for r in rs).items() if c>1];decls=a['declarations'];duplicates=[n for n,c in collections.Counter(d['name'] for d in decls).items() if c>1];nonstandard=[d for d in decls if set(d['axioms'])-{'propext','Classical.choice','Quot.sound'}];explicit=sum(len(r['print_axioms']) for r in rs if r['exit_status']==0 and r['module'].startswith('RPz2_Audit'));source=[r for r in rs if not r['module'].startswith('RPz2_Audit')];audits=[r for r in rs if r['module'].startswith('RPz2_Audit')];top=g['modules']['Rc7_Top'];repo=E.parents[1]
out={'attempts':len(rs),'contiguous_1_through_budget':numbers==list(range(1,601)),'lean_budget':600,'kani_runs':0,'source_attempts':len(source),'source_passed':sum(r['exit_status']==0 for r in source),'audit_attempts':len(audits),'audit_passed':sum(r['exit_status']==0 for r in audits),'passed_total':sum(r['exit_status']==0 for r in rs),'failed':[{k:r[k] for k in ['attempt','module','exit_status']} for r in rs if r['exit_status']!=0],'wall_seconds_sum':sum(r['wall_seconds'] for r in rs),'max_peak_rss_kib':max(int(r['peak_rss_kib']) for r in rs),'swap_sum':sum(int(r['swaps']) for r in rs),'duplicate_targets':dup_targets,'audit_modules':len(a['modules']),'queried_declarations':len(decls),'receipt_regex_print_axioms_count':explicit,'raw_print_axioms_results_in_audits':sum(sum('depends on axioms:' in l or 'does not depend on any axioms' in l for l in (E/r['attempt']/'stdout.log').read_text().splitlines()) for r in audits),'repeated_global_declaration_names':duplicates,'distinct_global_declaration_names':len({d['name'] for d in decls}),'duplicate_owner_name_queries':[list(k) for k,v in collections.Counter((d['module'],d['name']) for d in decls).items() if v>1],'nonstandard_declaration_dependencies':nonstandard,'standard_axiom_gate_passed':not nonstandard,'globally_unique_query_names':not duplicates,'missing_audit_modules':a['audit_missing_successful_replay_modules'],'unknown_import_headers':{m:x['unknown_import_headers'] for m,x in a['modules'].items() if x['unknown_import_headers']},'rc7_source_unchanged':hashlib.sha256((repo/top['source']).read_bytes()).hexdigest()==top['sha256'],'errors':errors,'qualification':'Only fresh subset audited. No fresh top theorem proof term, joint non-vacuity or source-to-ELF reproduction.'}
(E/'RPz2_final-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['nonstandard_declaration_dependencies','repeated_global_declaration_names','unknown_import_headers']},indent=2))
