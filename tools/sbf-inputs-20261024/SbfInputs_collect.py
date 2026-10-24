#!/usr/bin/env python3
"""Collect only new bounded public preparation receipts/manifests; no builds."""
import hashlib,json,pathlib,resource,shlex,subprocess,sys,time
E=pathlib.Path('evidence/sbf-inputs-20261024');start=time.monotonic();r=json.loads((E/'prepare.stdout.json').read_text());rows=[]
for key,name in [('output','preparation.json'),('manifest','registry-files.jsonl')]:
 pin=r[key];remote=pin['path'];assert remote.endswith('/'+name) and '/SbfInputs-20261024-v3/' in remote
 script='import pathlib,resource,sys,hashlib;resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));p=pathlib.Path('+repr(remote)+');assert not p.is_symlink() and p.stat().st_size<=5000000;b=p.read_bytes();assert hashlib.sha256(b).hexdigest()=='+repr(pin['sha256'])+';sys.stdout.buffer.write(b)'
 cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3 -B -c '+shlex.quote(script)]
 t=time.monotonic();p=subprocess.run(cmd,capture_output=True,timeout=30)
 row=dict(command=cmd,exit=p.returncode,wall_seconds=time.monotonic()-t,bytes=len(p.stdout),sha256=hashlib.sha256(p.stdout).hexdigest());rows.append(row)
 assert p.returncode==0 and not p.stderr and len(p.stdout)==pin['bytes'] and row['sha256']==pin['sha256']
 with (E/name).open('xb') as f:f.write(p.stdout)
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
out=dict(command=[sys.executable,'-B',__file__],results=rows,exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swap=u.ru_nswap+c.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A')
with (E/'collect.receipt.json').open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({k:v for k,v in out.items() if k!='results'}))
