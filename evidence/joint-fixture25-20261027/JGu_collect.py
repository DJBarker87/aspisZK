from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[];passed={}
for f in sorted(P.glob('JGu25_*/receipt.json')):
 r=json.loads(f.read_text());name=r['sources'][0];sha=r['source_hashes'][name]
 row={k:r[k] for k in ['attempt','source_revision','source_tree_dirty','exit_status','wall_seconds','peak_rss_kib','swaps','command','source_hashes','print_axioms','limits','cgroup','deps_fingerprint']}
 row['receipt']=str(f.relative_to(R));row['target']=name;rows.append(row)
 if r['exit_status']==0:
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    names=re.search(r'\[([^]]*)\]',line).group(1).replace(' ','').split(',')
    assert set(names)<=set(['propext','Classical.choice','Quot.sound']),line
  passed[(name,sha)]=r['attempt']
(P/'JGu_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
files=[]
for f in sorted((R/'lean').glob('JGu_*.lean')):
 sha=hashlib.sha256(f.read_bytes()).hexdigest();a=passed.get((f.name,sha))
 files.append(dict(module=f.stem,source_sha256=sha,passing_attempt=a,status='checked' if a else 'DRAFT / not delivered as checked'))
(P/'JGu_SOURCES.json').write_text(json.dumps(files,indent=2)+'\n')
summary=dict(lean_processes=len(rows),passing_processes=sum(r['exit_status']==0 for r in rows),nonpassing_processes=sum(r['exit_status']!=0 for r in rows),kani_runs=0,total_wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows),checked_current_modules=sum(bool(f['passing_attempt']) for f in files),draft_current_modules=sum(not f['passing_attempt'] for f in files),budget_max_lean=100,budget_max_kani=10,preflight_only_attempts=['JGu25_004'],top_removed=dict(T=0,P=0,G=0,C=0),full_joint_nonvacuity=False,accepted1=False,accepted2=False,shipped_source_changes=False,elf_rebuild_trigger=False,fresh_manifest_replay=False)
summary.update(launch_attempts=len(list(P.glob('JGu25_[0-9][0-9][0-9].json'))),budget_exhausted=len(list(P.glob('JGu25_[0-9][0-9][0-9].json')))>=100,budget_accounting='100 launch attempts;004 failed dependency preflight before Lean, so99 actual Lean processes; conservative100/100 budget. No101st launch.',maximum_successful_rss_kib=max(int(r['peak_rss_kib']) for r in rows if r['exit_status']==0),next_obligation='outer native batch_tree adapters and full batch0 source gate; then query0-9, flush, returned writer equality,accepted1 and joint fixture')
(P/'JGu_FAILURES.json').write_text(json.dumps([r for r in rows if r['exit_status']!=0],indent=2)+'\n')
(P/'JGu_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['preflight_only_attempts']}))
