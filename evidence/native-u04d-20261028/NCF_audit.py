"""Audit own receipts without replaying any prover."""
from pathlib import Path
import json,re,hashlib,subprocess,collections
E=Path(__file__).resolve().parent
rows=[json.loads(p.read_text()) for p in sorted(E.glob('NCF_[KL]*/receipt.json'))]
versions={x['module_sha256'] for x in json.loads((E/'NCF_SOURCE_VERSIONS.json').read_text())}
summary=collections.Counter();table=[]
for r in rows:
 a=r['attempt'];log=(E/a/'stdout.log').read_text();kind=r['kind']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
 if kind=='kani':
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  g=json.loads((E/(a+'-graph.json')).read_text());assert g['graph_matches_frozen'] and g['lock_unchanged'] and g['lock_before_sha256']==g['lock_after_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert g['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  if 'NBU_src/crates/aspis-statement/src/pool_v1/NCF_slots.rs' in r['source_hashes']:
   assert r['source_hashes']['NBU_src/crates/aspis-statement/src/pool_v1/NCF_slots.rs'] in versions,(a,'source snapshot missing')
  n=int(a[-3:]);failed=re.search(r'\*\* (\d+) of (\d+) failed',log)
  if n in [22,23]:status='EXCLUDED wrong own source capacity'
  elif 'unwinding assertion' in log:status='EXCLUDED unwinding failure'
  elif 'CAR size is less' in log:status='EXCLUDED contract CAR failure'
  elif n in [59,66]:status='EXCLUDED control: extra ghost precondition failure'
  elif n in [58,61,65,67]:status='provisional PASS; callee postcondition control invalid'
  elif 'unexpectedly panicked' in log:status='EXCLUDED compiler ICE'
  elif 'Checking harness' not in log:status='EXCLUDED compilation/input failure'
  elif r['exit_status']==0:status='PASS local component'
  elif failed and failed[1]=='1' and 'undetermined' not in log:status='expected semantic negative control'
  else:status='UNRESOLVED failure; no credit'
 else:
  status='PASS standard-axiom theorem' if r['exit_status']==0 and 'sorryAx' not in log else 'EXCLUDED elaboration failure'
 summary[status]+=1;table.append(dict(attempt=a,status=status,exit=r['exit_status'],wall=r['wall_seconds'],rss=r['peak_rss_kib'],swap=r['swaps'],axioms=r['print_axioms']))
(E/'NCF_AUDIT.json').write_text(json.dumps(dict(summary=dict(summary),attempts=table,whole_slot_closures=0),indent=2)+'\n')
print(json.dumps(dict(summary=dict(summary),receipts=len(rows))))
