"""Read-only receipt/source audit; emits exact transition remainder and run index."""
from pathlib import Path
import hashlib,json,re,collections
E=Path(__file__).resolve().parent;D=E.parent/'kani-reverify4-20261028'
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
STUB='c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9'
def read(p):return json.loads(p.read_text())
def write(n,x):(E/n).write_text(json.dumps(x,indent=2)+'\n')
def key(r):return (r['len'],r['cap'],r['size'])
def main():
 schedule=read(D/'KND_SCHEDULE.json');assert len(schedule)==len({key(r) for r in schedule})==116
 old=read(D/'KND_PAIRS.json');pairs=read(E/'KNE_PAIRS.json');assert len(pairs)<=75
 covered={key(p['transition']) for p in old if p['credit']};assert len(covered)==43
 checks=[];windows=collections.defaultdict(list);runindex=[];quarantine=[]
 for p in pairs:
  a,b=p['positive_id'],p['control_id'];ca,cb=read(E/(a+'.json')),read(E/(b+'.json'))
  ra,rb=read(E/a/'receipt.json'),read(E/b/'receipt.json')
  sa=(E/'sources'/(read(E/a/'classification.json')['source_sha256']+'.rs')).read_text()
  sb=(E/'sources'/(read(E/b/'classification.json')['source_sha256']+'.rs')).read_text()
  matched=sa.replace(' ^ 0u8',' ^ 1u8')==sb
  assert matched and 'fn KND_transition()' in sa
  for name,source,receipt in [(a,sa,ra),(b,sb,rb)]:
   digest=hashlib.sha256(source.encode()).hexdigest()
   assert digest==read(E/name/'classification.json')['source_sha256']
   assert digest==receipt['source_hashes']['KNE_windows.rs']
  for field in ['kind','env','timeout','sources','transition','index_window','deps_fingerprint']:
   assert ca[field]==cb[field],(a,field)
  failed='Failed Checks: assertion failed: out[j] ==' in (E/b/'stdout.log').read_text()
  control_only_xor=failed and '}) ^ 1u8' in (E/b/'stdout.log').read_text()
  credit=p['positive']=='PASS' and p['control']=='COUNTEREXAMPLE' and matched and control_only_xor
  assert credit==p['credit'],a
  if credit:windows[key(p['transition'])].append(p['index_window'])
  checks.append(dict(positive=a,control=b,transition=p['transition'],window=p['index_window'],matched=matched,only_xor1_diff=True,control_failed_selected_assertion=control_only_xor,credit=credit))
  for cfg,receipt in [(ca,ra),(cb,rb)]:
   run=cfg['attempt'];g=read(E/(run+'-graph.json'));assert g['allowed'] and not g['new_packages'] and not g['edge_errors']
   assert g['lock_before']==LOCK
   assert cfg['deps_fingerprint']['frozen_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
   if 'lock_after' in g:assert g['lock_after']==LOCK and g['unchanged']
   if p['credit']:assert g['lock_after']==LOCK and g['unchanged']
   assert cfg['env']['CARGO_NET_OFFLINE']=='true' and 'opt-level=3' in cfg['env']['RUSTFLAGS']
   assert receipt['source_hashes']['KMX_stubs.rs']==STUB
   assert 'Option<fn' not in (sa if run==a else sb)
 for triple,ws in windows.items():
  end=triple[0]+triple[2];mask=set()
  for lo,hi in ws:
   assert 0<=lo<hi<=end
   mask.update(range(lo,hi))
  if mask==set(range(end)):covered.add(triple)
 for rp in sorted(E.glob('KNE_[KL][0-9][0-9][0-9]/receipt.json')):
  r=read(rp);a=r['attempt'];ad=read(E/(a+'-reservation.json'))
  assert ad['allowed'] is True
  barrier=(E/(a+f"-barrier-{r['reservation_retries']}.log")).read_text();assert '"allowed": true' in barrier
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  if r['kind']=='lean':
   assert '-M7000' in r['command']
   if r['exit_status']==0:
    assert r['print_axioms'] and not any('sorryAx' in x for x in r['print_axioms'])
    for line in r['print_axioms']:
     found=re.search(r'axioms: \[([^]]*)\]',line)
     if found:assert set(x.strip() for x in found.group(1).split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'}
  assert str(r['swaps'])=='0'
  runindex.append({k:r[k] for k in ['attempt','kind','sources','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','cgroup','limits']})
 write('KNE_PAIR_AUDIT.json',checks)
 remainder=[r for r in schedule if key(r) not in covered]
 write('KNE_REMAINING_RUNTIME.json',remainder)
 write('KNE_COVERAGE.json',dict(total=116,prior=43,new=len(covered)-43,covered=len(covered),remaining=len(remainder),new_pairs=len(pairs),statuses=dict(collections.Counter(read(p)['result'] for p in E.glob('KNE_K*/classification.json'))),quarantine=quarantine,window_union={str(k):v for k,v in windows.items()}))
 write('KNE_RUNS.json',runindex)
 resources=[]
 for item in runindex:
  r=read(E/item['attempt']/'receipt.json');ad=read(E/(r['attempt']+'-reservation.json'))
  resources.append(dict(attempt=r['attempt'],allowed=ad['allowed'],admission_exit_guard='KMY_host.admit returns only after exit0 AND allowed:true',bounded_reserved_bytes=ad.get('bounded_reserved_bytes'),limits=r['limits'],peak_rss_kib=int(r['peak_rss_kib']),cgroup_memory_peak_bytes=int(r['cgroup_memory_peak_bytes']),swaps=r['swaps']))
 write('KNE_RESOURCE_AUDIT.json',dict(admission_implementation='../kani-reverify1-20261028/KMY_host.py',admission_implementation_sha256=hashlib.sha256((D.parent/'kani-reverify1-20261028/KMY_host.py').read_bytes()).hexdigest(),max_rss_kib=max(r['peak_rss_kib'] for r in resources),max_cgroup_memory_peak_bytes=max(r['cgroup_memory_peak_bytes'] for r in resources),all_swaps_zero=True,runs=resources))
 print(json.dumps(dict(covered=len(covered),remaining=len(remainder),pairs=len(pairs),runs=len(runindex))))
if __name__=='__main__':main()
