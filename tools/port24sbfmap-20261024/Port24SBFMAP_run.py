#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,time,resource
root=Path(__file__).resolve().parents[2];d=root/'evidence/port24sbfmap-20261024';p=Path(__file__).with_name('Port24SBFMAP_collect.py');b=p.read_bytes()
t=time.monotonic();cmd=['ssh','-o','BatchMode=yes','dombarker@100.108.41.90','python3','-']
r=subprocess.run(cmd,input=b,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
u=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt={'command':cmd,'script_sha256':hashlib.sha256(b).hexdigest(),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'exit_status':r.returncode,'wall_seconds':time.monotonic()-t,'peak_rss_bytes_local_ssh':u.ru_maxrss,'swaps_local_ssh':u.ru_nswap,'print_axioms':'N/A: read-only inspection','stderr':r.stderr.decode()}
(d/'inspection-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
if r.returncode:raise SystemExit(r.stderr.decode())
x=json.loads(r.stdout);x['inspection_receipt']['script_sha256']=receipt['script_sha256']
assert len(r.stdout)<5_000_000
(d/'selected-implementation.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({'builds':list(x['builds']),'input_count':len(x['inputs']),'bytes':len(r.stdout),'receipt':x['inspection_receipt']},indent=2))
