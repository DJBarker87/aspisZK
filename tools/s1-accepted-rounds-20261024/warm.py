#!/usr/bin/env python3
"""Reuse only the two exact checked-trace producer objects, never rebuild them."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021/s1-accepted-rounds-numeric-20261024';E.mkdir(exist_ok=True)
c=Path('/tmp/s126-round-trace-reused-20261024');c.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=[]
for n,packet in [('ExtractedSemanticRoundCheckedSuccess','source-semantic-round-checked-success-20261019'),('ExtractedSemanticRoundsCheckedTrace','source-ten-semantic-rounds-checked-trace-20261019')]:
 receipt=B/'evidence'/packet/n/'receipt.json';r=json.loads(receipt.read_text());p=c/(n+'.olean');s=B/'lean'/(n+'.lean')
 assert sha(s)==r['source_sha256'],n
 remote='/home/dombarker/project-offloads/terminal-v4-begin-mu-canonical-v1-20261019/prebuilt/'+n+'.olean'
 if not p.exists():subprocess.run(['scp','-q','dombarker@100.108.41.90:'+remote,str(p)],check=True)
 assert sha(p)==r['object_sha256'],(n,sha(p),r['object_sha256'])
 rows.append(dict(module=n,source=str(s.relative_to(R)),source_sha256=sha(s),object_sha256=sha(p),producer_receipt=str(receipt.relative_to(R)),producer_receipt_sha256=sha(receipt),remote=remote))
(E/'reused-trace.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',modules=rows),indent=2)+'\n')
Path('/tmp/s126-round-trace-path-20261024.txt').write_text(str(c)+':'+Path('/tmp/s126-finish-lean-path-20261024.txt').read_text().strip()+'\n')
print(json.dumps(dict(reused=len(rows))))
