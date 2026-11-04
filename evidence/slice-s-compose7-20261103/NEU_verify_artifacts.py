"""Final evidence integrity audit; no proof rerun or new status promotion."""
from pathlib import Path
from collections import Counter
import json,hashlib,re,datetime
import NEU_bridge_checks as b
E=Path(__file__).resolve().parent
rlist=[];sources=0
for p in sorted(E.glob('NEU_[KL]*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0 and float(r['wall_seconds'])>0 and int(r['peak_rss_kib'])>0
 assert len(r['source_revision'])==40
 if a.startswith('NEU_K'):
  inputs=b.inputs(E,a);assert set(inputs)==set(r['source_hashes'])
  assert all(hashlib.sha256(t.encode()).hexdigest()==r['source_hashes'][n] for n,t in inputs.items()),a
  ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
  lock=json.loads((E/(a+'-lock-check.json')).read_text());assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  log=(E/a/'stdout.log').read_text()
  kind='pass' if r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log else 'timeout' if r['exit_status']==124 or 'timed out' in log.lower() else 'failing control' if 'Failed Checks:' in log else 'excluded compile/input failure'
 else:
  src=(E/a/'NEU_SOURCE.lean.txt').read_bytes();assert hashlib.sha256(src).hexdigest()==r['source_hashes']['NEU_generated/'+r['module'].replace('.','/')+'.lean']
  if r['exit_status']==0:
   assert all('sorryAx' not in x for x in r['print_axioms'])
   for x in r['print_axioms']:
    if 'depends on axioms:' in x:
     found=x.split('depends on axioms:',1)[1].strip().strip('[]');assert not found or set(found.split(', '))<={'propext','Classical.choice','Quot.sound'},x
  kind='checked standard axioms' if r['exit_status']==0 else 'excluded elaboration'
 sources+=len(r['source_hashes']);rlist.append(dict(attempt=a,classification=kind,exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],cgroup_memory_peak_bytes=r.get('cgroup_memory_peak_bytes'),swaps=r['swaps'],source_revision=r['source_revision'],target=r['module'],print_axioms=r['print_axioms']))
assert {r['attempt'] for r in rlist if r['attempt'].startswith('NEU_K')}=={f'NEU_K{i:03}' for i in range(1,131)}
assert not (E/'NEU_ACTIVE.json').exists()
assert len((E/'NEU_ATTEMPTS.jsonl').read_text().splitlines())==len(rlist)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),native_attempts=130,lean_attempts=sum(r['attempt'].startswith('NEU_L') for r in rlist),classifications=dict(Counter(r['classification'] for r in rlist)),hashed_source_inputs=sources,all_execution_inputs_retained=True,limits_unchanged=True,standard_axioms_on_successful_targets=True,attempts=rlist)
(E/'NEU_EVIDENCE_AUDIT.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='attempts'}))
