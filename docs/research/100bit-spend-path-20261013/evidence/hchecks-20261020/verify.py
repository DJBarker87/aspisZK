#!/usr/bin/env python3
"""Verify receipt consistency without repeating a Lean build."""
import hashlib,json,pathlib,re
packet=pathlib.Path(__file__).resolve().parent
root=packet.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[]
for path in sorted(packet.glob('*/receipt.json')):
 r=json.loads(path.read_text());raw=(path.parent/'output.log').read_text()
 r['axioms']=re.findall(r"'[^'\n]+' (?:depends on axioms: \[.*?\]|does not depend on any axioms)",raw,re.S)
 r['deps_fingerprint']=sha(json.dumps(r['imports'],sort_keys=True).encode())
 path.write_text(json.dumps(r,indent=2)+'\n');receipts.append(r)
 if r['exit']==0:
  assert r['swaps']==0
  for audit in r['axioms']:
   if '[' in audit:assert set(x.strip() for x in audit.split('[',1)[1].rstrip(']').split(',')) <= {'propext','Classical.choice','Quot.sound'},audit
final={}
for r in receipts:
 source=root/'docs/research/100bit-spend-path-20261013/lean'/(r['module']+'.lean')
 if r['exit']==0 and sha(source.read_bytes())==r['source_sha256']:final[r['module']]=r
expected={'HchecksReaderComposition','HchecksPublicComposition','HchecksDecisionObstruction','HchecksAudit','HchecksAccumulator'}
assert set(final)==expected, set(final)
assert len(final['HchecksAudit']['axioms'])==5
(packet/'manifest.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':receipts},indent=2)+'\n')
summary=[{k:r[k] for k in ['module','attempt','source_sha256','source_revision','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axioms']} for r in final.values()]
(packet/'accepted-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
