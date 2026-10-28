"""Upload only this job's cfg(kani) module, after admission; no prover launch."""
from pathlib import Path
import sys,importlib.util,json,hashlib,subprocess,time
E=Path(__file__).resolve().parent
candidate=sys.argv[1];assert Path(candidate).name.startswith('NCC_')
sys.argv=['ncc','none'];s=importlib.util.spec_from_file_location('ncc',E/'NCC_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit('NCC_UPLOAD_'+Path(candidate).stem)
text=(E/candidate).read_text();before=hashlib.sha256((E/'NCC_slots.rs.txt').read_bytes()).hexdigest();after=hashlib.sha256(text.encode()).hexdigest()
payload='''from pathlib import Path
import hashlib,json
p=Path(%r)/'NBU_src/crates/aspis-statement/src/pool_v1/NCC_slots.rs'
before=hashlib.sha256(p.read_bytes()).hexdigest();p.write_text(%r)
after=hashlib.sha256(p.read_bytes()).hexdigest();assert after==%r
print(json.dumps(dict(path=str(p),before=before,after=after,prover_submitted=False)))
'''%(m.B,text,after)
for n in range(11):
 try:r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',m.H,'python3 -'],input=payload,capture_output=True,text=True,timeout=90)
 except subprocess.TimeoutExpired:
  with (E/'NCC_UPLOAD_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(candidate=candidate,trial=n,actual_exit=None,transport_timeout_seconds=90,prover_submitted=False))+'\n')
  if n<10:time.sleep(60);continue
  raise SystemExit('STOP prelaunch upload exhausted')
 with (E/'NCC_UPLOAD_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(candidate=candidate,trial=n,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,prover_submitted=False))+'\n')
 if r.returncode!=255:break
 if n<10:time.sleep(60)
assert r.returncode==0,r.stderr
(E/(Path(candidate).stem+'-upload.json')).write_text(r.stdout)
print(r.stdout)
