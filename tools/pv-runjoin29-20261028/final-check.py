"""Validate this run's exact receipts, source snapshots and discharge boundary."""
from pathlib import Path
import json,hashlib,re,subprocess,datetime,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin29-20261028';allowed={'propext','Classical.choice','Quot.sound'}
rows=[]
for p in E.glob('receipt-[0-9]*.json'):
 r=json.loads(p.read_text());r['receipt_file']=p.name
 assert hashlib.sha256((E/r['source_snapshot']).read_bytes()).hexdigest()==r['source_sha256']
 blob=subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']]);assert hashlib.sha256(blob).hexdigest()==r['source_sha256']
 assert r['source_git_blob']==subprocess.check_output(['git','rev-parse',r['source_revision']+':'+r['source_path']],text=True).strip()
 cmd=r['command'];assert all(x in cmd for x in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64','7000'])
 if r['accepted']:
  assert r['exit']==0 and r['swaps']==0 and r['axioms']
  for a in r['axioms']:
   assert 'sorryAx' not in a
   if 'depends on axioms:' in a:
    assert set(re.search(r'axioms: \[([^]]*)\]',a,re.S)[1].replace('\n','').replace(' ','').split(','))<=allowed
 tim=(E/f"time-{r['attempt']}.log").read_text();m=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)',tim)
 r['host_wall']=m[1].strip() if m else None;assert r['host_wall'] and r['peak_rss_bytes'] is not None
 rows.append(r)
rows.sort(key=lambda r:r['attempt'])
charged=sum(r['exit'] is not None for r in rows);assert charged<=64
if '--final' in sys.argv:assert charged==64,(charged,'authorized attempts must be spent unless a real stop is documented')
latest={r['source_path']:r for r in rows if r['accepted']}
status=[]
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RunJoin_*29.lean'):
 rel=str(p.relative_to(R));r=latest.get(rel);same=bool(r and hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'])
 status.append(dict(path=rel,accepted_source=same,attempt=r['attempt'] if r else None));assert same,rel
 s=p.read_text();assert not re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide|implemented_by)\b|set_option\s+(maxRecDepth|maxHeartbeats|debug\.skipKernelTC)',s,re.M),rel
assert not subprocess.check_output(['git','diff','a4e8f7dbad','--','crates','programs'])
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-runjoin-20261026'
assert R.resolve()==Path('/Users/dominic/ZK/.worktrees/pv-runjoin')
external=json.loads((E/'external-hash-check.json').read_text());assert len(external)==5673 and all(r['match'] for r in external)
if '--final' in sys.argv:
 for name in ['generate-statements.py','generate-errors.py','split-decoder.py','generate-codec-domain.py']:
  subprocess.run([sys.executable,str(R/'tools/pv-runjoin29-20261028'/name),'--check'],check=True)
 res=json.loads((E/'focused-resolution.json').read_text());assert not res['unpinned'] and not any(m.startswith('XR') or m.split('.')[-1].startswith('XR') for m in res['resolved'])
 cache=json.loads((E/'focused-project-cache-check.json').read_text());assert all(r.get('source_match') or r.get('retained_own_cache_source_match') for r in cache)
 assert json.loads((E/'replay-cache-h6-check.json').read_text())['all_match']
# Refused IDs are retired; only fresh IDs after the mandatory 180-second wait.
used=sorted([json.loads(p.read_text()) for p in E.glob('used-*.json')],key=lambda r:r['utc'])
intervals=[]
for p in E.glob('refusal-[0-9]*.json'):
 f=json.loads(p.read_text());stamp=datetime.datetime.fromisoformat(f['utc'])
 later=[u for u in used if datetime.datetime.fromisoformat(u['utc'])>stamp]
 if later:
  u=later[0];delta=(datetime.datetime.fromisoformat(u['utc'])-stamp).total_seconds()
  assert delta>=180,(p.name,delta)
  intervals.append(dict(refusal=p.name,next_attempt=u['attempt'],seconds=delta))
(E/'admission-intervals.json').write_text(json.dumps(intervals,indent=2)+'\n')
for p in E.glob('id-audit-*.json'):
 a=json.loads(p.read_text());assert not a['other_receipt_hits'] and not a['sent_hits'],p.name
seen=set()
for r in rows:
 key=(r['source_sha256'],r['deps_fingerprint']);assert key not in seen,key;seen.add(key)
summary=dict(charged=charged,accepted=sum(r['accepted'] for r in rows),rejected=sum(not r['accepted'] for r in rows),remaining=64-charged,kani=0,refusals=len(list(E.glob('refusal-[0-9]*.json'))),source_status=status,peak_rss_bytes=max(r['peak_rss_bytes'] for r in rows),all_swaps_zero=all(r['swaps']==0 for r in rows),endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_weakened=0,target_established=False)
(E/'tally.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'receipt-index.tsv').write_text('attempt\ttarget\texit\thost_wall\tssh_wall_s\tpeak_rss_bytes\tswap\tsource_revision\taccepted\n'+''.join('\t'.join(str(r.get(k,'')) for k in ['attempt','target','exit','host_wall','wall_seconds','peak_rss_bytes','swaps','source_revision','accepted'])+'\n' for r in rows))
print(json.dumps({k:v for k,v in summary.items() if k!='source_status'},indent=2))
