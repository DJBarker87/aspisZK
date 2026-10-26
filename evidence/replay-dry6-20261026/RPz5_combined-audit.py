"""Combine only unchanged-context inherited audits with new current-cohort audits."""
from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent;R=E.parents[1]
old=json.loads((R/'evidence/replay-dry5-20261026/RPz4_axiom-audit.json').read_text());new=json.loads((E/'RPz5_axiom-audit.json').read_text())
keep=set(json.loads((E/'RPz5_reuse.json').read_text())['state']);p=json.loads((E/'RPz5_source-plan.json').read_text());s=json.loads((E/'RPz5_state.json').read_text())['state']
assert keep<=set(old['covered_modules'])
assert not keep&set(new['covered_modules'])
olddecl=[{**v,'coverage_basis':'RPz4 unchanged transitive source/object context'} for v in old['declarations'] if v['module'] in keep]
newdecl=[{**v,'coverage_basis':'RPz5 selected smaller-cohort fresh source context'} for v in new['declarations']]
d=olddecl+newdecl;std={'propext','Classical.choice','Quot.sound'};bad=[v for v in d if set(v['axioms'])-std];covered=keep|set(new['covered_modules']);passed={m for m in p['order'] if s.get(m)=='passed'}
errors=[]
if covered!=passed:errors.append('green-context coverage mismatch')
if new['audit_completion_errors'] or new['source_import_header_mismatches'] or new['passed_modules_missing_audit']:errors.append('fresh audit failed or incomplete')
if any(n>1 for n in collections.Counter((v['module'],v['name']) for v in d).values()):errors.append('duplicate owner/name query')
nonformatter=[v for v in bad if 'CoreFmtDebug' not in v['name']]
if nonformatter:errors.append('nonstandard axiom outside observed formatter definitions')
out={'inherited_contexts':len(keep),'fresh_contexts':len(new['covered_modules']),'green_contexts_covered':len(covered),'inherited_declaration_queries_reused':len(olddecl),'fresh_declaration_queries':len(newdecl),'combined_queries':len(d),'distinct_global_names':len({v['name'] for v in d}),'repeated_global_names':{k:n for k,n in collections.Counter(v['name'] for v in d).items() if n>1},'declarations':d,'nonstandard_queries':bad,'nonstandard_modules':dict(collections.Counter(v['module'] for v in bad)),'nonstandard_axioms':sorted({a for v in bad for a in v['axioms'] if a not in std}),'nonformatter_nonstandard_queries':nonformatter,'all_declaration_standard_only_gate':not bad,'missing_green_contexts':sorted(passed-covered),'errors':errors,'fresh_top_axioms':'NOT REACHED','fresh_top_formatter_reachability':'UNKNOWN: source closure blocked by incompatible Phase owners','qualification':'Reused declarations retain their exact historical raw print-axioms output and unchanged transitive context; no repeated-name proof-term identity is inferred. No claim covers blocked source vertices or fresh top reachability.'}
(E/'RPz5_combined-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:out[k] for k in ['inherited_contexts','fresh_contexts','green_contexts_covered','combined_queries','nonstandard_modules','errors']});print('nonstandard axiom count',len(out['nonstandard_axioms']))
