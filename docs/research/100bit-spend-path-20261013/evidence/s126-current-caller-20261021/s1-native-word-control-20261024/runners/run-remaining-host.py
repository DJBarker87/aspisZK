#!/usr/bin/env python3
from pathlib import Path
import json,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');r=H/'run-partition-host.py';W=H/'s1-claim-word-partition-v1-20261024';plan=H/'s1-word-partition-remaining-v1.json';assert not plan.exists()
rows=[]
for point in [6,1,2,3,4]:
 name=f's1-original-word-partition-point{point}-bounded-v1'
 assert not (H/'receipts'/name).exists(),name
 rows.append(dict(point=point,name=name,command=['python3',str(r),name,str(W),f'proofs::original_and_owned_first_error_point_{point}','stubbing','short',str(point)]))
plan.write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',runner_sha256=hashlib.sha256(r.read_bytes()).hexdigest(),jobs=rows,policy='Sequential; each child performs fresh admission and creates its own capped zero-swap scope. Stop on first nonzero outcome.'),indent=2)+'\n')
for row in rows:
 p=subprocess.run(row['command'])
 if p.returncode:raise SystemExit(p.returncode)
