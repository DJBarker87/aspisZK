"""Check the final focused receipts; no replay or source mutation."""
from pathlib import Path
import json,hashlib,re,subprocess,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin27-20261027'
assert str(R)=='/Users/dominic/ZK/.worktrees/pv-runjoin'
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-runjoin-20261026'
assert not subprocess.check_output(['git','diff','d6bc54e213','--','crates/','programs/'],cwd=R)
rows=[]
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text());a=r['attempt'];src=R/r['source_path']
 b=subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']],cwd=R)
 assert hashlib.sha256(b).hexdigest()==r['source_sha256']
 assert hashlib.sha256((E/r['source_snapshot']).read_bytes()).hexdigest()==r['source_sha256']
 t=(E/f'time-{a}.log').read_text();m=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',t)
 sec=0
 if m:
  for part in m[1].strip().split(':'):sec=sec*60+float(part)
 r['host_wall_seconds']=sec
 assert r['swaps']==0 and r['peak_rss_bytes']<8*2**30 and r['reservation']['allowed']
 if r['accepted']:
  assert r['exit']==0 and 'sorryAx' not in str(r['axioms'])
  for line in r['axioms']:
   m=re.search(r'depends on axioms: \[([\s\S]*?)\]',line)
   if m:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',m[1])) <= {'propext','Classical.choice','Quot.sound'}
 p.write_text(json.dumps(r,indent=2)+'\n');rows.append(r)
status=[]
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RunJoin_*27.lean'):
 h=hashlib.sha256(p.read_bytes()).hexdigest();accepted=[r['attempt'] for r in rows if r['accepted'] and r['source_sha256']==h]
 assert accepted,(str(p),h)
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^\s*axiom\s',p.read_text(),re.M)
 status.append(dict(path=str(p.relative_to(R)),sha256=h,accepted_attempts=accepted))
native=[]
for p in sorted(E.glob('pv27-zero-change-*/receipt.json')):
 r=json.loads(p.read_text());assert r['swaps']==0 and r['scope_swap_peak_bytes'] in [None,'0']
 assert r['controls']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert '--release' in r['target']
 for path,h in r['source_sha256'].items():
  b=subprocess.check_output(['git','show',r['worker_revision']+':'+path],cwd=R);assert hashlib.sha256(b).hexdigest()==h
  (p.parent/(Path(path).name+'.source.txt')).write_bytes(b)
 if r['exit']==0:
  s=(p.parent/'out.log').read_text();assert 'control=Ok' in s and 'full_withdrawal=Err(Conservation)' in s
 native.append(dict(path=str(p.relative_to(R)),exit=r['exit'],wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=r['swaps']))
assert any(r['exit']==0 for r in native)
refusals=[dict(path=str(p.relative_to(R)),**json.loads(p.read_text())) for p in E.glob('*refusal*.json')]
used=[json.loads(p.read_text()) for p in E.glob('used-*.json')]
for r in refusals:
 t=datetime.datetime.fromisoformat(r['utc'])
 later=[datetime.datetime.fromisoformat(u['utc']) for u in used if datetime.datetime.fromisoformat(u['utc'])>t]
 if later:assert (min(later)-t).total_seconds()>=180,(r['path'],min(later))
resolved=json.loads((E/'focused-resolution.json').read_text());assert not resolved['unpinned']
assert not any(m.startswith('XR') or m.split('.')[-1].startswith('XR') for m in resolved['resolved'])
assert all(r['match'] for r in json.loads((E/'external-hash-check.json').read_text()))
assert json.loads((E/'replay-cache-h6-check.json').read_text())['all_match']
assert not json.loads((E/'native-source-check.json').read_text())['mismatches']
(E/'proof-status.json').write_text(json.dumps(status,indent=2)+'\n')
(E/'receipt-index.tsv').write_text('attempt\ttarget\texit\taccepted\thost_wall_seconds\tpeak_rss_bytes\tswaps\tsource_revision\tsource_sha256\n'+''.join('\t'.join(str(r.get(k,'')) for k in ['attempt','target','exit','accepted','host_wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256'])+'\n' for r in rows))
tally=dict(charged_lean=len(rows),accepted_lean=sum(r['accepted'] for r in rows),rejected_lean=[r['attempt'] for r in rows if not r['accepted']],remaining_lean_budget=59-len(rows),kani=0,local_lean=0,native=native,refusals=refusals,ids_retired=[r['attempt'] for r in used],unused_focus_ids=sorted(set(range(38141,38194))-{r['attempt'] for r in used}),standard_axioms=True,shipped_source_unchanged=True,target_established=False,stop='checked admitted-domain/native-preparation counterexample')
(E/'tally.json').write_text(json.dumps(tally,indent=2)+'\n');print(json.dumps({k:v for k,v in tally.items() if k not in ['refusals','unused_focus_ids']}))
