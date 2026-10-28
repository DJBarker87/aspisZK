from NBO_host import *
import sys,subprocess,time,json,fcntl
serial=(E/'NBO_SERIAL.lock').open('a');fcntl.flock(serial,fcntl.LOCK_EX)
a=sys.argv[1];admit(a)
r=py(f'''from pathlib import Path
b=Path({B!r});src=b/'NBO_src';old=Path('/home/dombarker/project-offloads/codex-cx-native-query2-20261027/NBF_src')
if not src.exists():src.symlink_to(old,target_is_directory=True)
f=src/'crates/aspis-r1-cost-probe/src/candidate.rs';text=f.read_text();marker='\\n#[cfg(kani)] #[path="NBO_native.rs"] mod NBO_native;\\n'
if marker not in text:f.write_text(text+marker)
''')
assert r.returncode==0,r.stderr
argv=['scp','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',str(E/'NBO_native.rs.txt'),H+':'+B+'/NBO_src/crates/aspis-r1-cost-probe/src/NBO_native.rs']
for trial in range(11):
 r=subprocess.run(argv,capture_output=True,text=True)
 with (E/'NBO_NATIVE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,step='scp own module',trial=trial,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,submitted=False))+'\n')
 if r.returncode==0:break
 if r.returncode!=255 or trial==10:raise SystemExit('STOP own module transport '+r.stderr)
 print('prelaunch transport255; wait60s',flush=True);time.sleep(60)
r=py(f'''from pathlib import Path
import json,hashlib
src=Path({B!r})/'NBO_src';f=src/'crates/aspis-r1-cost-probe/src/candidate.rs';m=src/'crates/aspis-r1-cost-probe/src/NBO_native.rs'
print(json.dumps(dict(scratch=str(src.resolve()),reuse='terminal predecessor scratch; no second corpus',candidate_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),module_sha256=hashlib.sha256(m.read_bytes()).hexdigest())))
''')
assert r.returncode==0,r.stderr
(E/(a+'-source.json')).write_text(r.stdout)
