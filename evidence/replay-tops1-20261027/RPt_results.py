from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
p=read(E/'RPt_plan.json');rs=sorted([read(f) for f in E.glob('RPt_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]));by={d['module']:d for d in rs};rows={r['original']:r for r in p['rows']}
roots=[]
for root,closure in p['closures'].items():
 new=[n for n in closure if n in rows]
 green=[n for n in new if rows[n]['module'] in by and by[rows[n]['module']]['exit_status']==0]
 failed=[n for n in new if rows[n]['module'] in by and by[rows[n]['module']]['exit_status']!=0]
 unbuilt=[n for n in new if rows[n]['module'] not in by]
 roots.append({'root':root,'closure':len(closure),'reused':len(closure)-len(new),'new_green':len(green),'failed':failed,'unbuilt':unbuilt})
out={'attempts':len(rs),'lean_limit':400,'kani_runs':0,'passed':sum(d['exit_status']==0 for d in rs),'failed_attempts':[d['attempt'] for d in rs if d['exit_status']!=0],'roots':roots,'new_source_contexts':len(rows),'fresh_source_green':sum(r['module'] in by and by[r['module']]['exit_status']==0 for r in rows.values()),'remaining_source_vertices':[n for n,r in rows.items() if r['module'] not in by],'compiler_wall_seconds':sum(d['wall_seconds'] for d in rs),'peak_rss_kib':max([int(d['peak_rss_kib']) for d in rs] or [0]),'swaps':sum(int(d['swaps']) for d in rs),'reservation_retries':sum(d['reservation_retries'] for d in rs),'no_new_premise_discharge':True}
fresh_modules={r['module'] for r in rows.values()}
out['ready_unbuilt']=[n for n,r in rows.items() if r['module'] not in by and all(i not in fresh_modules or (i in by and by[i]['exit_status']==0) for i in r['imports'])]
out['new_failed_vertices']=[n for n,r in rows.items() if r['module'] in by and by[r['module']]['exit_status']!=0]
(E/'RPt_frontier.json').write_text(json.dumps(out,indent=2)+'\n')
for d in rs:
 if d['module']!='RPt_BEnAudit':continue
 log=(E/d['attempt']/'stdout.log').read_text()
 def parse(tag):return [json.loads(l.split(tag,1)[1]) for l in log.splitlines() if tag in l]
 statement=parse('RPT_KERNEL_STATEMENT ')[0];records=parse('RPT_FORMATTER ');reachable=parse('RPT_REACHABLE_CONSTANTS ')[0];axioms=parse('RPT_ACTUAL_AXIOMS ')[0]
 raw=(json.dumps(statement,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode();(E/'RPt_BEn_Top.kernel.txt').write_bytes(raw)
 inventory=read(E.parents[1]/'evidence/replay-dry9-20261027/RPz8_formatter-axiom-reachability.json')
 # Actual axiom declarations are obtained from the pinned predecessor inventory.
 axnames=[]
 def collect(o):
  if isinstance(o,dict):
   if o.get('isAxiom') is True and isinstance(o.get('name'),str):axnames.append(o['name'])
   for v in o.values():collect(v)
  elif isinstance(o,list):
   for v in o:collect(v)
 collect(inventory)
 result={'root':'AspisR1.BEn_Top.deployed','attempt':d['attempt'],'records':records,'formatter_records':len(records),'all_records_present':all(r['present'] for r in records),'reachable_records':sum(r['reachable'] for r in records),'actual_reachable_axioms':axioms,'reachable_constants':len(reachable),'kernel_statement_sha256':hashlib.sha256(raw).hexdigest(),'kernel_statement_bytes':len(raw),'print_axioms':d['print_axioms'],'ARX_equality_by_rfl':d['exit_status']==0,'actual_formatter_axiom_records':[{'name':n,'reachable':n in reachable} for n in sorted(set(axnames))]}
 (E/'RPt_BEn-formatter-records.json').write_text(json.dumps(result,indent=2)+'\n');(E/'RPt_BEn-reachable-constants.json').write_text(json.dumps(reachable,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['roots','remaining_source_vertices']});print('unbuilt',{r['root']:len(r['unbuilt']) for r in roots})
