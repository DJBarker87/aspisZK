from pathlib import Path
import json,subprocess,hashlib,re,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin25-20261027'
rows=[]
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text());a=r['attempt'];rel=r['source_path']
 b=subprocess.check_output(['git','show',r['source_revision']+':'+rel],cwd=R)
 assert hashlib.sha256(b).hexdigest()==r['source_sha256'],a
 assert hashlib.sha256((E/r['source_snapshot']).read_bytes()).hexdigest()==r['source_sha256'],a
 r['source_matches_git_revision']=True
 tim=(E/f'time-{a}.log').read_text();m=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',tim)
 if m:
  seconds=0
  for x in m[1].strip().split(':'):seconds=seconds*60+float(x)
  r['host_wall_seconds']=seconds
 assert r['swaps']==0 and r['reservation']['allowed'] and r['peak_rss_bytes']<8*1024**3,a
 if r['accepted']:
  for ax in r['axioms']:
   m=re.search(r'depends on axioms: \[([\s\S]*?)\]',ax)
   if m:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',m[1])) <= {'propext','Classical.choice','Quot.sound'},(a,ax)
  assert r['exit']==0 and 'sorryAx' not in str(r['axioms'])
 p.write_text(json.dumps(r,indent=2)+'\n');rows.append(r)
assert str(R)=='/Users/dominic/ZK/.worktrees/pv-runjoin'
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-runjoin-20261026'
assert not subprocess.check_output(['git','diff','0df6024f36','--','crates/','programs/'],cwd=R)
used=[json.loads(p.read_text()) for p in E.glob('used-*.json')]
assert all(38129<=r['attempt']<=38193 for r in used)
for p in E.glob('refusal-*.json'):
 r=json.loads(p.read_text());a=int(p.stem.split('-')[1]);t=datetime.datetime.fromisoformat(r['utc'])
 after=[x for x in used if x['attempt']>a]
 if after:
  n=min(after,key=lambda x:x['attempt']);delta=(datetime.datetime.fromisoformat(n['utc'])-t).total_seconds();assert delta>=180,(a,delta)
status=[]
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RunJoin_*25.lean'):
 sha=hashlib.sha256(p.read_bytes()).hexdigest();matches=[r['attempt'] for r in rows if r['accepted'] and r['source_sha256']==sha]
 assert matches,(str(p),sha)
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^\s*axiom\s',p.read_text(),re.M),p
 status.append(dict(path=str(p.relative_to(R)),sha256=sha,accepted_attempts=matches))
(E/'proof-status.json').write_text(json.dumps(status,indent=2)+'\n')
(E/'receipt-index.tsv').write_text('attempt\ttarget\texit\taccepted\thost_wall_seconds\tpeak_rss_bytes\tswaps\tsource_revision\tsource_sha256\n'+''.join('\t'.join(str(r.get(k,'')) for k in ['attempt','target','exit','accepted','host_wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256'])+'\n' for r in rows))
out=dict(charged=len(rows),accepted=sum(r['accepted'] for r in rows),rejected=[r['attempt'] for r in rows if not r['accepted']],refusals=sorted(int(p.stem.split('-')[1]) for p in E.glob('refusal-*.json')),ids_retired=len(used),unused_authorized_ids=sorted(set(range(38129,38194))-{r['attempt'] for r in used}),remaining_lean_budget=70-len(rows),kani=0,local_lean=0,peak_rss_bytes=max(r['peak_rss_bytes'] for r in rows),swaps=0,axioms_standard_for_accepted=True,shipped_diff_empty=True,current_accepted_sources=len(status),formal_release_claim=False)
(E/'tally.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
