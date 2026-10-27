from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;R=E.parents[1];read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
p=read(E/'RPu_plan.json');rs=sorted([read(f) for f in E.glob('RPu_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]));by={d['module']:d for d in rs};rows={r['original']:r for r in p['rows']};roots=[]
for root,closure in p['closures'].items():
 new=[n for n in closure if n in rows];green=[n for n in new if rows[n]['module'] in by and by[rows[n]['module']]['exit_status']==0];failed=[n for n in new if rows[n]['module'] in by and by[rows[n]['module']]['exit_status']!=0];unbuilt=[n for n in new if rows[n]['module'] not in by]
 roots.append({'root':root,'closure':len(closure),'reused':len(closure)-len(new),'new_green':len(green),'failed':failed,'unbuilt':unbuilt})
out={'attempts':len(rs),'lean_limit':500,'kani_runs':0,'passed':sum(d['exit_status']==0 for d in rs),'failed_attempts':[d['attempt'] for d in rs if d['exit_status']!=0],'roots':roots,'new_source_contexts':len(rows),'fresh_source_green':sum(r['module'] in by and by[r['module']]['exit_status']==0 for r in rows.values()),'remaining_source_vertices':[n for n,r in rows.items() if r['module'] not in by],'compiler_wall_seconds':sum(d['wall_seconds'] for d in rs),'peak_rss_kib':max([int(d['peak_rss_kib']) for d in rs] or [0]),'swaps':sum(int(d['swaps']) for d in rs),'reservation_retries':sum(d['reservation_retries'] for d in rs),'no_new_premise_discharge':True}
fresh_modules={r['module'] for r in rows.values()}
out['ready_unbuilt']=[n for n,r in rows.items() if r['module'] not in by and all(i not in fresh_modules or (i in by and by[i]['exit_status']==0) for i in r['imports'])]
out['new_failed_vertices']=[n for n,r in rows.items() if r['module'] in by and by[r['module']]['exit_status']!=0]
union=set().union(*(set(c) for c in p['closures'].values()));out['root_union_repository_contexts']=len(union);out['root_union_green_contexts']=len([n for n in union if n not in rows or (rows[n]['module'] in by and by[rows[n]['module']]['exit_status']==0)])
(E/'RPu_frontier.json').write_text(json.dumps(out,indent=2)+'\n')
for d in rs:
 if not d['module'].endswith('_TopAudit') or d['exit_status']!=0:continue
 root=d['module'][4:-5];name='AspisR1.'+root+'.deployed';log=(E/d['attempt']/'stdout.log').read_text()
 def parse(tag):return [json.loads(l.split(tag,1)[1]) for l in log.splitlines() if tag in l]
 statement=parse('RPU_KERNEL_STATEMENT ')[0];records=parse('RPU_FORMATTER ');reachable=parse('RPU_REACHABLE_CONSTANTS ')[0];axioms=parse('RPU_ACTUAL_AXIOMS ')[0]
 raw=(json.dumps(statement,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode();(E/f'RPu_{root}.kernel-expr.json').write_bytes(raw)
 m=re.search('BEGIN KERNEL TYPE '+re.escape(name)+r'\n(.*?)\nEND KERNEL TYPE '+re.escape(name),log,re.S);assert m,name
 pretty='-- Complete kernel type of '+name+'\n'+m.group(1).strip()+'\n';assert '⋯' not in pretty and '...' not in pretty
 (E/f'RPu_{root}.kernel.lean.txt').write_text(pretty)
 inventory=read(R/'evidence/replay-tops1-20261027/RPt_BEn-formatter-records.json');axnames=[r['name'] for r in inventory['actual_formatter_axiom_records']]
 result={'root':name,'attempt':d['attempt'],'records':records,'formatter_records':len(records),'all_records_present':all(r['present'] for r in records),'reachable_records':sum(r['reachable'] for r in records),'actual_reachable_axioms':axioms,'reachable_constants':len(reachable),'kernel_statement_sha256':sha(raw),'kernel_statement_bytes':len(raw),'print_axioms':d['print_axioms'],'actual_formatter_axiom_records':[{'name':n,'reachable':n in reachable} for n in axnames]}
 (E/f'RPu_{root}-formatter-records.json').write_text(json.dumps(result,indent=2)+'\n');(E/f'RPu_{root}-reachable-constants.json').write_text(json.dumps(reachable,indent=2)+'\n')
 # First #check uses the original job's default printer settings. That historical
 # output contains ellipses; the independent full kernel artifacts above do not.
 n=root[:3];job={'FJp':'finish-match4','FJu':'finish-chain1'}[n];a={'FJp':'097','FJu':'022'}[n];oldpath=R/f'evidence/{job}-20261027/{n}_{a}/stdout.log';old=oldpath.read_text()
 def block(t):
  ls=t[t.index('@'+name+' :'):].splitlines();stop=next((i for i,l in enumerate(ls[1:],1) if l and not l[0].isspace()),len(ls));return '\n'.join(ls[:stop]).rstrip()+'\n'
 b=block(old).encode();f=block(log).encode();(E/f'RPu_{root}.job-format.txt').write_bytes(f)
 comparisons={'root':name,'job_statement_path':str(oldpath.relative_to(R)),'job_output_sha256':sha(oldpath.read_bytes()),'historical_default_check_bytes':len(b),'historical_default_check_sha256':sha(b),'fresh_default_check_sha256':sha(f),'byte_identical_default_check':b==f,'historical_default_check_truncated':'⋯' in b.decode(),'full_fresh_kernel_artifact':f'RPu_{root}.kernel.lean.txt','fresh_full_pretty_sha256':sha(pretty.encode())}
 if n=='FJu':
  path=R/'evidence/stack1-20261027/FJv_before_top.kernel.lean.txt';comparisons.update(full_historical_path=str(path.relative_to(R)),full_historical_sha256=sha(path.read_bytes()),full_pretty_byte_identical=path.read_bytes()==pretty.encode())
 (E/f'RPu_{root}-statement-comparison.json').write_text(json.dumps(comparisons,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['roots','remaining_source_vertices','ready_unbuilt']});print('unbuilt',{r['root']:len(r['unbuilt']) for r in roots})
