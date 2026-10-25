#!/usr/bin/env python3
import hashlib,json,pathlib,resource,subprocess,time
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-cache-prep-20261024';start=time.monotonic();p=T/'SbfCachePrep_inventory.py';body=p.read_bytes()
assert json.loads((E/'proc.stdout.json').read_text())['allowed_to_enter']
assert not (E/'inventory.stdout.json').exists()
cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3 -']
r=subprocess.run(cmd,input=body,capture_output=True,timeout=60)
(E/'inventory.stdout.json').write_bytes(r.stdout);(E/'inventory.stderr.txt').write_bytes(r.stderr)
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt=dict(command=cmd,exit=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(body).hexdigest(),transport_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),stdout_sha256=hashlib.sha256(r.stdout).hexdigest(),stderr_sha256=hashlib.sha256(r.stderr).hexdigest(),print_axioms='N/A')
(E/'inventory.transport.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if r.returncode:print(r.stderr.decode());raise SystemExit(r.returncode)
print(r.stdout.decode())
