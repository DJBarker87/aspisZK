from pathlib import Path
import hashlib,json,re,subprocess,datetime,sys
partial="--partial" in sys.argv
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin28-20261027'
assert R==Path('/Users/dominic/ZK/.worktrees/pv-runjoin')
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-runjoin-20261026'
assert not subprocess.check_output(['git','diff','d73d800f26','--name-only','--','crates','programs'],text=True).strip()
rows=[];accepted={};allowed={'propext','Classical.choice','Quot.sound'}
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text());snap=E/r['source_snapshot'];assert hashlib.sha256(snap.read_bytes()).hexdigest()==r['source_sha256']
 blob=subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']]);assert blob==snap.read_bytes()
 out=(E/f"out-{r['attempt']}.log").read_text();tim=(E/f"time-{r['attempt']}.log").read_text()
 assert r['command'][0]=='systemd-run' and all(x in r['command'] for x in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64','7000'])
 assert r['swaps']==0 and r['shared_sources_written']==False
 elapsed=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)',tim)
 if elapsed:
  parts=elapsed[1].split(':');v=0.0
  for part in parts:v=v*60+float(part)
  r['host_wall_seconds']=v
  p.write_text(json.dumps(r,indent=2)+'\n')
 if r['accepted']:
  assert r['exit']==0 and 'sorryAx' not in out and 'error:' not in out
  for block in r['axioms']:
   if 'depends on axioms:' in block:
    names=set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',block.split('depends on axioms:',1)[1]));assert names<=allowed,(p,names)
  current=R/r['source_path'];assert current.read_bytes()==snap.read_bytes()
  assert not re.search(r'\b(?:sorry|admit|native_decide|implemented_by)\b',current.read_text())
  assert not re.search(r'^\s*axiom\s',current.read_text(),re.M)
  assert not re.search(r'^import\s+(?:\S*\.)?XR',current.read_text(),re.M)
  accepted[r['target']]=r
 rows.append(r)
(E/'receipt-index.tsv').write_text('attempt\ttarget\texit\thost_wall_seconds\tssh_wall_seconds\tpeak_rss_bytes\tswaps\tsource_revision\taccepted\n'+''.join('\t'.join(str(r.get(k,'')) for k in ['attempt','target','exit','host_wall_seconds','wall_seconds','peak_rss_bytes','swaps','source_revision','accepted'])+'\n' for r in rows))
resolution=json.loads((E/'focused-resolution.json').read_text());assert not resolution['unpinned']
assert all(r['match'] for r in json.loads((E/'external-hash-check.json').read_text()))
assert json.loads((E/'replay-cache-h6-check.json').read_text())['all_match']
refusals=sorted([json.loads(p.read_text()) for p in E.glob('*refusal*.json')],key=lambda x:x['utc'])
for refusal in refusals:
 t=datetime.datetime.fromisoformat(refusal['utc'])
 # Every later consumed ID's admission log is timestamped by the actual reservation receipt.
 later=[]
 for q in list(E.glob('reservation-*.json'))+list(E.glob('refusal-*.json')):
  d=json.loads(q.read_text());u=datetime.datetime.fromisoformat(d['utc'])
  if u>t:later.append(u)
 if later:assert (min(later)-t).total_seconds()>=179,(refusal,min(later))
retired=sorted(int(p.stem.split('-')[-1]) for p in E.glob('used-*.json'))
assert all(38146<=a<=38193 for a in retired)
subprocess.run(['python3',str(R/'tools/pv-runjoin28-20261027/check-native-result.py')],check=True)
for p in E.glob('pv28-*/receipt.json'):
 n=json.loads(p.read_text());assert n['exit']==0 and n['swaps']==0
 assert n['controls']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for f,h in n['source_sha256'].items():assert hashlib.sha256((R/f).read_bytes()).hexdigest()==h
zero=E/'pv28-zero-recipient-01/out.log'
if zero.is_file():assert 'zero_recipient=Err(Conservation)' in zero.read_text()
if not partial:assert zero.is_file(), 'zero recipient native receipt missing'
required=['CompilerDomainProof28','RejectionProof28','FrontierHonesty28','PairValidity28','ZeroRecipient28','ActiveFrontier28','PreparedPayload28','CanonicalFrontier28','DomainAudit28']
pending=[n for n in required if 'R1Z/PV_RunJoin_'+n not in accepted]
if not partial:assert not pending,pending
cache=json.loads((E/'focused-project-cache-check.json').read_text())
if not partial:assert all(r.get('source_match') or r.get('retained_own_cache_source_match') for r in cache)
status=dict(pending_validation=pending,partial=partial,charged_lean=len(rows),accepted_lean=sum(r['accepted'] for r in rows),rejected_lean=[r['attempt'] for r in rows if not r['accepted']],remaining_lean_budget=57-len(rows),ids_retired=retired,unused_focus_ids=[a for a in range(38146,38194) if a not in retired],kani=0,local_lean=0,standard_axioms=True,shipped_source_unchanged=True,target_established=False,stop='checked fresh raw compiler success / HonestInput frontier counterexample; intended canonical-route provenance and full outer domain remain open',native=[dict(path=str(p.relative_to(E)),**{k:json.loads(p.read_text()).get(k) for k in ['exit','wall_seconds','peak_rss_bytes','swaps']}) for p in E.glob('pv28-*/receipt.json')])
(E/'tally.json').write_text(json.dumps(status,indent=2)+'\n')
(E/'proof-status.json').write_text(json.dumps({m:dict(attempt=r['attempt'],source_sha256=r['source_sha256'],axioms=r['axioms']) for m,r in accepted.items()},indent=2)+'\n')
print(json.dumps(status,indent=2))
