#!/usr/bin/env python3
"""Read-only recovery of a submitted scope's result files (never resubmits). usage: PCQI_recover.py PCQI_L025 TARGET"""
import subprocess,sys,json,base64,lzma,hashlib,shlex
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-pc-prov-p1i-20261110'
a,target=sys.argv[1:3]
code=f'''from pathlib import Path
import json,base64,hashlib
b=Path({B!r});a={a!r};names=[p for p in (b/a).rglob('*') if p.is_file()]+[b/(a+'.json')]
p=b/'PCQI_exports'/({target!r}+'.olean')
if p.exists():
 q=b/(a+'-object.json');q.write_text(json.dumps(dict(module={target!r},path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)));names.append(q)
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in names}}))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=20','-o','ServerAliveInterval=15',H,'timeout 300 bash -c '+shlex.quote('python3 -c '+shlex.quote(code))],capture_output=True,text=True)
if r.returncode:print('FAIL',r.returncode,r.stderr[-200:]);sys.exit(1)
for n,v in json.loads(r.stdout).items():
    raw=base64.b64decode(v);p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
    if (len(raw)>1_000_000 or n.endswith(('stdout.log','time.log'))) and not n.endswith('.xz'):
        p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
    else:p.write_bytes(raw)
print('recovered',a)
