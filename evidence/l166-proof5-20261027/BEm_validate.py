"""Read-only task evidence audit; runs no compiler or proof tool."""
from pathlib import Path
import hashlib,json,collections,subprocess,re
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for p in sorted(P.glob('BEm_*/receipt.json')):
 d=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
 verified=d['kind']=='kani' and d['exit_status']==0 and log.count('VERIFICATION SUCCESSFUL')==1 and 'VERIFICATION FAILED' not in log
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},(p,d['limits'])
 assert str(d['swaps'])=='0'
 if d['kind']=='lean' and d['exit_status']==0:
  assert 'sorryAx' not in log and 'error:' not in log
  for line in d.get('print_axioms',[]):
   names=re.search(r'axioms: \[(.*)\]',line)
   assert names,line
   for name in names.group(1).split(', '):
    name=re.sub(r'\.\{[^}]*\}','',name)
    assert name in ('','propext','Classical.choice','Quot.sound'),line
 for f,h in d.get('source_hashes',{}).items():
  source=p.parent/'sources'/f
  assert source.exists() and sha(source.read_bytes())==h,(p,f)
 rows.append(dict(attempt=d['attempt'],kind=d['kind'],exit=d['exit_status'],wall=d['wall_seconds'],rss_kib=d['peak_rss_kib'],cgroup_peak_bytes=d.get('cgroup_memory_peak_bytes'),swaps=d['swaps'],revision=d['source_revision'],verified=verified,axioms=d.get('print_axioms')))
counts=collections.Counter(x['kind'] for x in rows)
assert counts['kani']<=20 and counts['lean']<=100 and counts['charon']+counts['aeneas']<=4
old=(R/'evidence/l166-proof4-20261027/BEl_rust/src/BEl_frozen.rs').read_bytes()
raw=(P/'BEm_rust/src/BEm_frozen.rs').read_bytes()
wrapper=(P/'BEm_parent_wrappers.rs').read_bytes()
assert raw.count(wrapper)==1
new=raw.replace(b'\n'+wrapper,b'').replace(b'BEm_',b'BEl_')
assert old==new,'Frozen source cuts changed beyond prefix spelling'
result=dict(attempts=rows,counts=counts,kani_verified=sum(x['verified'] for x in rows),frozen_cut_normalized_sha256=sha(new),removed=[],added=[],L166='OPEN',model_agreement='not established',physical_association='not established')
(P/'BEm_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
