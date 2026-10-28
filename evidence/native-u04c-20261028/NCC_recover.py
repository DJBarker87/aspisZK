"""Read-only recovery; no prover launch or resubmission."""
from pathlib import Path
import importlib.util,sys,json,zlib,base64,time,hashlib
E=Path(__file__).resolve().parent
args=sys.argv[1:];sys.argv=['ncc','none'];s=importlib.util.spec_from_file_location('ncc',E/'NCC_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
names=[]
for a in args:names += [a+'.json',a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph.json',a+'-metadata.stderr',a+'-reservation.json']+[a+'-barrier-'+str(i)+'.log' for i in range(11)]
code='''from pathlib import Path
import json,zlib,base64
b=Path(%r);names=%r
x={n:(b/n).read_text() for n in names if (b/n).is_file()}
print(base64.b64encode(zlib.compress(json.dumps(x).encode(),9)).decode())
'''%(m.B,names)
for trial in range(11):
 r=m.py(code);assert r.returncode==0,r.stderr
 try:x=json.loads(zlib.decompress(base64.b64decode(r.stdout)))
 except Exception as exc:
  with (E/'NCC_RECOVERY_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,error=str(exc),stdout_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),read_only=True))+'\n')
  if trial<10:time.sleep(60);continue
  raise SystemExit('STOP recovery retries exhausted')
 break
existing={json.loads(l)['attempt'] for l in (E/'NCC_ATTEMPTS.jsonl').read_text().splitlines()}
for n,data in x.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(data)
for a in args:
 assert a+'/receipt.json' in x,('unresolved receipt',a)
 rc=json.loads(x[a+'/receipt.json'])
 if a not in existing:
  with (E/'NCC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
 print(a,rc['exit_status'],rc['wall_seconds'],rc['peak_rss_kib'])
with (E/'NCC_RECOVERY_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempts=args,read_only=True,compressed_bytes=len(r.stdout),recovered_files=len(x)))+'\n')
