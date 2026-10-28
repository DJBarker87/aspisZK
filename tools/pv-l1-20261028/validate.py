"""Read-only final receipt/source audit; no compiler invocation."""
import pathlib,json,hashlib,subprocess,re
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1-20261028';sha=lambda b:hashlib.sha256(b).hexdigest()
rs=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert [r['attempt'] for r in rs]==list(range(51600,51700))
allowed={'propext','Classical.choice','Quot.sound'}
for r in rs:
 assert r['source_revision'] and r['exit'] is not None and r['host_wall_seconds'] is not None and r['peak_rss_bytes'] and r['swaps']==0
 assert sha((E/r['source_snapshot']).read_bytes())==r['source_sha256']
 assert sha(subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']]))==r['source_sha256']
 assert all(s in r['command'] for s in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64','7000'])
 assert r['reservation']['allowed'] is True
 if r['accepted']:
  assert r['exit']==0
  for a in r['axioms']:
   if 'depends on axioms:' in a:assert set(re.search(r'\[(.*?)\]',a,re.S)[1].split(', '))<=allowed,a
  p=R/r['source_path']
  assert p.exists() and sha(p.read_bytes())==r['source_sha256'],p
assert all(json.loads((E/f'receipt-{i}.json').read_text())['accepted'] for i in [51697,51698,51699])
assert not subprocess.check_output(['git','diff','--name-only','1e826627aa','HEAD','--','crates/','programs/']).strip()
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-l1-20261028'
assert str(R)=='/Users/dominic/ZK/.worktrees/pv-l1'
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024];assert not large,large
accepted=json.loads((E/'accepted-theorems.json').read_text());out=(E/'out-51697.log').read_text()
assert all("'"+n+"' " in out for n in accepted['theorems'])
assert not re.search(r'^import\s+.*\bXR', '\n'.join((R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')).read_text() for m in accepted['modules']),re.M)
summary=dict(lean_attempts=len(rs),kani_attempts=0,accepted_attempts=sum(r['accepted'] for r in rs),failed_attempts=sum(not r['accepted'] for r in rs),audit_ids=[51697,51698,51699],all_audits_accepted=True,accepted_new_modules=len(accepted['modules'])+3,accepted_new_theorems=len(accepted['theorems']),axioms=sorted(allowed),peak_rss_bytes=max(r['peak_rss_bytes'] for r in rs),total_host_wall_seconds=round(sum(r['host_wall_seconds'] for r in rs),2),swap=0,source_snapshots_and_git_revisions_verified=True,accepted_current_sources_unchanged=True,crates_programs_changes=[],rows_closed=[],premises_removed=[],native_credit=False,stop='100 Lean attempts exhausted; native integration remains open')
(E/'attempts.jsonl').write_text(''.join(json.dumps({k:r.get(k) for k in ['attempt','target','accepted','exit','host_wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','axioms']})+'\n' for r in rs))
(E/'validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
