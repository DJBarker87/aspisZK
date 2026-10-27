from pathlib import Path
import json,hashlib,re
from RPx_attempt import E,R
read=lambda p:json.loads(p.read_text());write=lambda n,x:(E/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
rs=sorted([read(f) for f in E.glob('RPx_*/receipt.json')],key=lambda d:d['attempt']);plan=read(E/'RPx_plan.json');by={d['module']:d for d in rs}
with (E/'RPx_attempts.jsonl').open('w') as f:
 for d in rs:f.write(json.dumps(d,ensure_ascii=False)+'\n')
summary=dict(lean_attempts=len(rs),lean_limit=150,kani_runs=0,passed=sum(d['exit_status']==0 for d in rs),failed=[d['attempt'] for d in rs if d['exit_status']!=0],source_contexts=len(plan['rows']),green_source_contexts=sum(by.get(r['module'],{}).get('exit_status')==0 for r in plan['rows']),compiler_wall_seconds=sum(d['wall_seconds'] for d in rs),peak_rss_kib=max(int(d['peak_rss_kib']) for d in rs),swaps=sum(int(d['swaps']) for d in rs),reservation_retries=sum(d['reservation_retries'] for d in rs),premises_removed=0,one_scope_at_a_time=True,shipped_changes=False)
write('RPx_summary.json',summary)
if 'RPx_DeployedAudit' not in by:print(summary);raise SystemExit()
d=by['RPx_DeployedAudit'];assert d['exit_status']==0;s=(E/d['attempt']/'stdout.log').read_text()
parse=lambda tag:[json.loads(l.split(tag,1)[1]) for l in s.splitlines() if tag in l]
statement=parse('RPX_KERNEL_STATEMENT ')[0];write('RPx_Deployed.kernel-expr.json',statement)
records=parse('RPX_FORMATTER ');reachable=parse('RPX_REACHABLE_CONSTANTS ')[0];axioms=parse('RPX_ACTUAL_AXIOMS ')[0]
assert set(axioms)<={'propext','Classical.choice','Quot.sound'},axioms
inventory=read(R/'evidence/replay-tops1-20261027/RPt_BEn-formatter-records.json');axnames=[r['name'] for r in inventory['actual_formatter_axiom_records']]
fmt=dict(root='AspisR1.RPx_Deployed.deployed',attempt=d['attempt'],records=records,formatter_records=len(records),all_records_present=all(r['present'] for r in records),reachable_records=sum(r['reachable'] for r in records),actual_reachable_axioms=axioms,actual_formatter_axiom_records=[dict(name=n,reachable=n in reachable) for n in axnames],retained_formatter_base_reachability=[dict(name=n,reachable=n in reachable) for n in ['Aeneas.Std.core.fmt.Formatter','Aeneas.Std.core.fmt.Formatter.write_str']],reachable_constants=len(reachable),print_axioms=d['print_axioms'])
write('RPx_formatter-records.json',fmt);write('RPx_reachable-constants.json',reachable)
assert len(records)==180 and fmt['all_records_present'] and fmt['reachable_records']==0
assert all(not r['reachable'] for r in fmt['actual_formatter_axiom_records'])
# Trace the actual root header, excluding audit-only imports.
headers={r['module']:r['imports'] for r in parse('RPX_IMPORTS ')}
pending=['RPx_Deployed'];seen=set()
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n);assert n in headers,n;pending+=headers[n]
old=read(R/'evidence/replay-tops3-20261027/RPv_plan.json');mapping=old['mapping'].copy()
for r in plan['rows']:mapping[r['original']]=r['module']
expected={mapping.get(n,n) for n in old['closures']['FJv_Deployed']}
historical_planned_contexts=len(expected)
# The pinned Phase transport support module has no original repository vertex.
# It is the sole additional selected context; its retained object/source pins
# were checked in the inherited cohort, and no source replacement is allowed.
expected.add('RPz7_PhaseIso')
missing=sorted(expected-seen)
selected_prefixes=('RPx_','RPv_','RPu_','RPt_','RPz8_','RPz7_')
extra=sorted(n for n in seen if n.startswith(selected_prefixes) and n not in expected)
closure=dict(root='RPx_Deployed',historical_planned_contexts=historical_planned_contexts,planned_contexts_including_transport=len(expected),explicit_retained_transport_support=['RPz7_PhaseIso'],actual_root_header_modules_including_libraries=len(seen),missing=missing,extra_replay_contexts=extra,all_37_fresh_contexts_reached=all(r['module'] in seen for r in plan['rows']),scope='Actual root dependency header traversal; independent audit imports excluded')
write('RPx_import-closure-check.json',closure);assert not missing and not extra and closure['all_37_fresh_contexts_reached'],closure
if 'RPx_DeclarationAudit' in by:
 d=by['RPx_DeclarationAudit'];assert d['exit_status']==0;s=(E/d['attempt']/'stdout.log').read_text()
 decls=[json.loads(l.split('RPX_DECL ',1)[1]) for l in s.splitlines() if 'RPX_DECL ' in l]
 covered={r['module'] for r in decls};expected={r['module'] for r in plan['rows']}
 bad=[r for r in decls if not set(r['axioms'])<={'propext','Classical.choice','Quot.sound'}]
 raw=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",s,re.M)
 raw_names={n for n,_ in raw}
 raw_lists={n:sorted(a.strip() for a in xs.split(',') if a.strip()) for n,xs in raw}
 raw_match=all(sorted(r['axioms'])==raw_lists.get(r['name']) for r in decls)
 audit=dict(attempt=d['attempt'],selected_contexts=len(expected),covered_contexts=len(covered),declarations=len(decls),missing_contexts=sorted(expected-covered),nonstandard_declarations=bad,raw_axiom_report_count=len(raw),raw_axiom_lists_match_structured_records=raw_match,missing_raw_axiom_reports=[r['name'] for r in decls if r['name'] not in raw_names],records=decls)
 write('RPx_declaration-audit.json',audit);assert not audit['missing_contexts'] and not bad and not audit['missing_raw_axiom_reports'] and raw_match,{k:v for k,v in audit.items() if k!='records'}
print(summary)
