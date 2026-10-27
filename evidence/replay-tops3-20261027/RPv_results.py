from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;R=E.parents[1];read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
p=read(E/'RPv_plan.json');rs=sorted([read(f) for f in E.glob('RPv_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]));by={d['module']:d for d in rs};rows={r['original']:r for r in p['rows']};roots=[]
for root,closure in p['closures'].items():
 new=[n for n in closure if n in rows];green=[n for n in new if rows[n]['module'] in by and by[rows[n]['module']]['exit_status']==0];failed=[n for n in new if rows[n]['module'] in by and by[rows[n]['module']]['exit_status']!=0];unbuilt=[n for n in new if rows[n]['module'] not in by]
 roots.append({'root':root,'closure':len(closure),'reused':len(closure)-len(new),'new_green':len(green),'failed':failed,'unbuilt':unbuilt})
out={'attempts':len(rs),'lean_limit':1100,'kani_runs':0,'passed':sum(d['exit_status']==0 for d in rs),'failed_attempts':[d['attempt'] for d in rs if d['exit_status']!=0],'roots':roots,'new_source_contexts':len(rows),'fresh_source_green':sum(r['module'] in by and by[r['module']]['exit_status']==0 for r in rows.values()),'remaining_source_vertices':[n for n,r in rows.items() if r['module'] not in by],'compiler_wall_seconds':sum(d['wall_seconds'] for d in rs),'peak_rss_kib':max([int(d['peak_rss_kib']) for d in rs] or [0]),'swaps':sum(int(d['swaps']) for d in rs),'reservation_retries':sum(d['reservation_retries'] for d in rs),'no_new_premise_discharge':True}
fresh_modules={r['module'] for r in rows.values()}
out['ready_unbuilt']=[n for n,r in rows.items() if r['module'] not in by and all(i not in fresh_modules or (i in by and by[i]['exit_status']==0) for i in r['imports'])]
out['new_failed_vertices']=[n for n,r in rows.items() if r['module'] in by and by[r['module']]['exit_status']!=0]
union=set().union(*(set(c) for c in p['closures'].values()));out['root_union_repository_contexts']=len(union);out['root_union_green_contexts']=len([n for n in union if n not in rows or (rows[n]['module'] in by and by[rows[n]['module']]['exit_status']==0)])
(E/'RPv_frontier.json').write_text(json.dumps(out,indent=2)+'\n')
for d in rs:
 if d['module'] not in ['RPv_FJv_TopAudit','RPv_FJv_DeployedAudit'] or d['exit_status']!=0:continue
 root=d['module'][4:-5];name='AspisR1.'+root+'.deployed';log=(E/d['attempt']/'stdout.log').read_text()
 def parse(tag):return [json.loads(l.split(tag,1)[1]) for l in log.splitlines() if tag in l]
 statement=parse('RPV_KERNEL_STATEMENT ')[0];records=parse('RPV_FORMATTER ');reachable=parse('RPV_REACHABLE_CONSTANTS ')[0];axioms=parse('RPV_ACTUAL_AXIOMS ')[0];assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(root,axioms)
 raw=(json.dumps(statement,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode();(E/f'RPv_{root}.kernel-expr.json').write_bytes(raw)
 m=re.search('BEGIN KERNEL TYPE '+re.escape(name)+r'\n(.*?)\nEND KERNEL TYPE '+re.escape(name),log,re.S);assert m,name
 pretty='-- Complete kernel type of '+name+'\n'+m.group(1).strip()+'\n';assert '⋯' not in pretty and '...' not in pretty
 (E/f'RPv_{root}.kernel.lean.txt').write_text(pretty)
 inventory=read(R/'evidence/replay-tops1-20261027/RPt_BEn-formatter-records.json');axnames=[r['name'] for r in inventory['actual_formatter_axiom_records']]
 result={'root':name,'attempt':d['attempt'],'records':records,'formatter_records':len(records),'all_records_present':all(r['present'] for r in records),'reachable_records':sum(r['reachable'] for r in records),'actual_reachable_axioms':axioms,'retained_formatter_base_reachability':[{'name':n,'reachable':n in reachable} for n in ['Aeneas.Std.core.fmt.Formatter','Aeneas.Std.core.fmt.Formatter.write_str']],'reachable_constants':len(reachable),'kernel_statement_sha256':sha(raw),'kernel_statement_bytes':len(raw),'print_axioms':d['print_axioms'],'actual_formatter_axiom_records':[{'name':n,'reachable':n in reachable} for n in axnames]}
 (E/f'RPv_{root}-formatter-records.json').write_text(json.dumps(result,indent=2)+'\n');(E/f'RPv_{root}-reachable-constants.json').write_text(json.dumps(reachable,indent=2)+'\n')
 historical=R/('evidence/stack1-20261027/FJv_after_'+('top' if root=='FJv_Top' else 'deployed')+'.kernel.lean.txt')
 comparison=dict(root=name,historical_path=str(historical.relative_to(R)),historical_sha256=sha(historical.read_bytes()),fresh_sha256=sha(pretty.encode()),byte_identical=historical.read_bytes()==pretty.encode(),complete_no_ellipsis=True)
 (E/f'RPv_{root}-statement-comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
 assert comparison['byte_identical'],comparison
print('attempts',len(rs),'pending',{r['root']:len(r['unbuilt']) for r in roots})
