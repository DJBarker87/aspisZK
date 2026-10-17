#!/usr/bin/env python3
"""Read/hash-only four-target source-run checkpoint verification."""
from pathlib import Path
import tarfile,json,hashlib
E=Path(__file__).resolve().parent;B=E.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();m=json.loads((E/'manifest.json').read_text());a=E/'source-full25-frames-accepted.tar.gz';assert sha(a.read_bytes())==m['archive_sha256']
with tarfile.open(a) as t:
 ss=json.load(t.extractfile('SHA256SUMS.json'));assert len(t.getmembers())==len(ss)+1==76;fs={n:t.extractfile(n).read() for n in ss}
 for n,b in fs.items():assert sha(b)==ss[n],n
 records={Path(n).stem:json.loads(b) for n,b in fs.items() if n.startswith('successful-targets/')};assert len(records)==4;count=0
 for n,d in records.items():
  assert d['exit_status']==0 and d['axioms']['passed'] and d['process_swaps']==0 and d['cgroup_swap_current']=='0'
  assert d['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
  assert sha(fs['sources/'+n+'.lean'])==d['key']['source_sha256'];assert sha(fs['objects/'+n+'.olean'])==d['objects']['.olean']['sha256']
  for dep,pin in d['key']['imports'].items():
   if dep in records:
    assert pin['receipt_key']==sha(json.dumps(records[dep]['key'],sort_keys=True).encode()) and pin['objects']==records[dep]['objects']
  for r in d['axioms']['reports']:assert set(r['axioms'])<={'propext','Classical.choice','Quot.sound'};count+=1
 assert count==24
 for n in ['ExtractedDigest32Transcript','ExtractedDigest32Callers','ExtractedDigest32Begin']:
  assert fs['sources/'+n+'.lean']==(B/'lean'/(n+'.lean')).read_bytes()
 assert fs['sources/ExtractedSourceFull25Frames.lean']==(B/'lean/bridge-source-full25-20261017/ExtractedSourceFull25Frames.lean').read_bytes()
 assert sha((B/'evidence/verify-helper-prefix-fe80-20261017/verify-helper-prefix-accepted.tar.gz').read_bytes())==m['canonical_predecessor_archive_sha256']
 print('PASS76members;4current coherent targets;24standard-only reports; constructed source frames; failed attempt excluded')
