#!/usr/bin/env python3
import subprocess,hashlib,json,time,resource,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];script=Path(sys.argv[1]);out=root/'evidence/sbf-identity-20261024'/sys.argv[2]
b=script.read_bytes();cmd=['ssh','-o','BatchMode=yes','dombarker@100.108.41.90','python3','-'];t=time.monotonic()
x=subprocess.run(cmd,input=b,capture_output=True);u=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt=dict(command=cmd,script=str(script),script_sha256=hashlib.sha256(b).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),exit=x.returncode,wall_seconds=time.monotonic()-t,peak_rss_bytes_local_transport=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A: metadata only',stderr=x.stderr.decode(),stdout_sha256=hashlib.sha256(x.stdout).hexdigest(),stdout_bytes=len(x.stdout))
out.with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
if len(x.stdout)<=5000000:out.write_bytes(x.stdout)
if x.returncode:raise SystemExit(x.stderr.decode())
print(json.dumps(receipt,indent=2))
