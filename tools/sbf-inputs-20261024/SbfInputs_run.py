#!/usr/bin/env python3
"""One-shot bounded Python SSH transport; only the committed literal helper runs."""
import hashlib,json,pathlib,resource,subprocess,sys,time
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-inputs-20261024';start=time.monotonic()
assert not (E/'prepare.transport.json').exists(),'no unchanged retry'
helper=T/'SbfInputs_prepare.py';body=helper.read_bytes();rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert subprocess.check_output(['git','show',rev+':tools/sbf-inputs-20261024/'+helper.name])==body
pk=(E/'packages.json').read_bytes()
request=dict(revision=rev,helper_sha256=hashlib.sha256(body).hexdigest(),packages=json.loads(pk),request_sha256=hashlib.sha256(pk).hexdigest())
# Helper reads exactly one following JSON line; exec code cannot consume package input.
# stdin cannot supply both Python - program and data; use exact quoted -c program.
import shlex
cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3 -B -c '+shlex.quote(body.decode())]
request['host_command']=['python3','-B','-c',body.decode()]
r=subprocess.run(cmd,input=(json.dumps(request)+'\n').encode(),capture_output=True,timeout=180)
assert len(r.stdout)<5_000_000 and len(r.stderr)<1_000_000
(E/'prepare.stdout.json').write_bytes(r.stdout);(E/'prepare.stderr.txt').write_bytes(r.stderr)
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt=dict(command=cmd,exit=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swap=u.ru_nswap+c.ru_nswap,source_revision=rev,helper_sha256=hashlib.sha256(body).hexdigest(),script_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),packages_sha256=hashlib.sha256(pk).hexdigest(),request_sha256=hashlib.sha256((json.dumps(request)+'\n').encode()).hexdigest(),stdout_sha256=hashlib.sha256(r.stdout).hexdigest(),stderr_sha256=hashlib.sha256(r.stderr).hexdigest(),print_axioms='N/A')
with (E/'prepare.transport.json').open('x') as f:json.dump(receipt,f,indent=2);f.write('\n')
print(r.stdout.decode());print(r.stderr.decode(),file=sys.stderr);sys.exit(r.returncode)
