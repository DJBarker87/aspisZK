from pathlib import Path
import subprocess,json,sys,time,re
B=Path.cwd();mode=sys.argv[1];assert re.fullmatch('proof[0-9]+',mode)
E=B/'LIBC_audit'/mode;E.mkdir(parents=True,exist_ok=True)
start=time.monotonic()
with (E/(mode+'.log')).open('w') as out:r=subprocess.run(['LIBC_native/LIBC_ProofDriver',mode],stdout=out,stderr=subprocess.STDOUT)
raw=(E/(mode+'.log')).read_text()
results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')]
(E/(mode+'.json')).write_text(json.dumps(dict(exit_status=r.returncode,wall_seconds=time.monotonic()-start,results=results),indent=1)+'\n')
print(json.dumps(dict(group=mode,exit=r.returncode,roots=len(results))),flush=True)
sys.exit(r.returncode)
