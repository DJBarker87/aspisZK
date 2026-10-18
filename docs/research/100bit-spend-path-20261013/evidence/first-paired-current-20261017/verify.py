#!/usr/bin/env python3
"""Read/hash-only exact named-discriminant repair and typedFull checkpoint."""
from pathlib import Path
import tarfile,json,hashlib
E=Path(__file__).resolve().parent;B=E.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();m=json.loads((E/'manifest.json').read_text());a=E/m['archive'];assert sha(a.read_bytes())==m['archive_sha256']
with tarfile.open(a) as t:
 ss=json.load(t.extractfile('SHA256SUMS.json'));assert len(t.getmembers())==len(ss)+1==m['members'];fs={n:t.extractfile(n).read() for n in ss}
 for n,b in fs.items():assert sha(b)==ss[n],n
 records={Path(n).stem:json.loads(b) for n,b in fs.items() if n.startswith('successful-targets/')};assert len(records)==1;count=0
 for n,d in records.items():
  assert d['exit_status']==0 and d['axioms']['passed'] and d['process_swaps']==0 and d['cgroup_swap_current']=='0'
  assert d['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
  assert sha(fs['sources/'+n.replace('.','/')+'.lean'])==d['key']['source_sha256'];assert sha(fs['objects/'+n.replace('.','/')+'.olean'])==d['objects']['.olean']['sha256']
  for dep,pin in d['key']['imports'].items():
   if dep in records:assert pin['receipt_key']==sha(json.dumps(records[dep]['key'],sort_keys=True).encode()) and pin['objects']==records[dep]['objects']
  for r in d['axioms']['reports']:assert set(r['axioms'])<={'propext','Classical.choice','Quot.sound'};count+=1
 assert count==1
 assert fs['sources/ExtractedFirstPairedReachability.lean']==(B/'lean/bridge-finish-a555-20261017/ExtractedFirstPairedReachability.lean').read_bytes()
 print('PASS1coherent target;1standard report; actual first yields same semantic/prepared values and actual finish/prepare calls')
