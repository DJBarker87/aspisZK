from pathlib import Path
import json,subprocess,hashlib,re
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-runjoin22-20261027'
hist={}
for name in ['audit-build-order.json','universal-build-order.json','remaining-build-order.json']:
 for x in json.loads((E/name).read_text()):hist[x['module']]=x['path']
rows=[]
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text());a=r['attempt'];m=r['target'];rel=r.get('source_path',hist.get(m,'docs/research/v8-r0-zk-20261009/lean/'+m+'.lean'))
 b=subprocess.check_output(['git','show',r['source_revision']+':'+rel],cwd=R)
 assert hashlib.sha256(b).hexdigest()==r['source_sha256'],(a,rel)
 assert hashlib.sha256((E/r['source_snapshot']).read_bytes()).hexdigest()==r['source_sha256'],a
 r['source_path']=rel;r['source_git_blob']=subprocess.check_output(['git','rev-parse',r['source_revision']+':'+rel],cwd=R,text=True).strip();r['source_matches_git_revision']=True
 tim=(E/f'time-{a}.log').read_text();mt=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',tim)
 if mt:
  value=mt[1].strip();seconds=0
  for v in value.split(':'):seconds=seconds*60+float(v)
  r['host_wall_elapsed']=value;r['host_wall_seconds']=seconds
 assert r['swaps']==0,a
 assert r['reservation']['allowed'] and r['peak_rss_bytes']<8*1024**3,a
 if r['accepted']:
  assert r['exit']==0 and all('sorryAx' not in s for s in r['axioms']),a
  for ax in r['axioms']:
   mm=re.search(r'depends on axioms: \[([\s\S]*?)\]',ax)
   if mm:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',mm[1])) <= {'propext','Classical.choice','Quot.sound'},(a,ax)
 p.write_text(json.dumps(r,indent=2)+'\n');rows.append(r)
assert subprocess.check_output(['git','branch','--show-current'],cwd=R,text=True).strip()=='codex/pv-runjoin-20261026'
assert str(R)=='/Users/dominic/ZK/.worktrees/pv-runjoin'
assert not subprocess.check_output(['git','diff','16de372145','--','crates/','programs/'],cwd=R)
used=[int(p.stem.split('-')[1]) for p in E.glob('used-*.json')]
assert len(used)==100 and set(used)==set(range(38900,39000)),used
assert len(rows)==99
assert [r['attempt'] for r in rows if r['attempt'] in [38997,38998,38999] and r['accepted']]==[38997,38998,38999]
assert (E/'refusal-38981.json').exists()
status=[]
L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
paths=list(L.glob('PV_RunJoin_Universal*22.lean'))+[L/'PV_RunJoin_PayloadAssociation22.lean']
paths += [L/p for p in ['PV_RunJoin_RecordsAdapter16.lean','PV_RunJoin_GeneralBranches16.lean','PV_RunJoin_BankRow17.lean','PV_RunJoin_ValueBits20.lean','PV_RunJoin_PublicBuildAudit22.lean','PV_RunJoin_TreeBankAudit22.lean','PV_RunJoin_SamplerAudit22.lean']]
for p in paths:
 sha=hashlib.sha256(p.read_bytes()).hexdigest();matches=[r['attempt'] for r in rows if r['source_sha256']==sha and r['accepted']]
 assert matches,(p,sha)
 text=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^\s*axiom\s',text,re.M),p
 status.append(dict(path=str(p.relative_to(R)),sha256=sha,accepted_attempts=matches))
(E/'proof-status.json').write_text(json.dumps(status,indent=2)+'\n')
(E/'receipt-index.tsv').write_text('attempt\ttarget\texit\taccepted\thost_wall_seconds\tpeak_rss_bytes\tswaps\tsource_revision\tsource_sha256\n'+''.join('\t'.join(str(r.get(k,'')) for k in ['attempt','target','exit','accepted','host_wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256'])+'\n' for r in rows))
out=dict(charged=len(rows),accepted=sum(r['accepted'] for r in rows),rejected=[r['attempt'] for r in rows if not r['accepted']],refusals=[38981],ids_retired=100,next_unused_authorized_id=None,remaining_nominal_lean_budget=1,kani=0,local_lean=0,peak_rss_bytes=max(r['peak_rss_bytes'] for r in rows),swaps=0,source_hashes_verified=True,axioms_standard_for_accepted=True,shipped_diff_empty=True,current_accepted_sources=len(status),formal_release_claim=False)
(E/'tally.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
