from pathlib import Path
import subprocess,json,hashlib,time,sys
E=Path(__file__).resolve().parent
OLD='/home/dombarker/project-offloads/codex-pv-integ4-20261027'
D='/home/dombarker/project-offloads/codex-pv-gate6-20261028'
HOST='dombarker@100.108.41.90'
REV='82566acdfb488183022f41ac564c11df22c9404f'
P=Path('tools/pv-integ4-20261027')
def remote(code):
 r=subprocess.run(['ssh',HOST,'python3','-'],input=code,text=True,capture_output=True)
 print(r.stdout,r.stderr,flush=True);r.check_returncode();return r.stdout
# Initial pre-upload refusal is retained. Wait three minutes before every retry.
for n in range(1,11):
 time.sleep(180)
 output=remote(f'''from pathlib import Path
import subprocess,json
D=Path({D!r});o=D/'upload-retry-{n:02d}';o.mkdir()
r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(o/'admission.json')],stdout=open(o/'output.log','w'),stderr=subprocess.STDOUT)
a=json.loads((o/'admission.json').read_text());print(json.dumps(dict(exit=r.returncode,allowed=a['allowed'])))
''')
 a=json.loads(output)
 if a['exit']==0 and a['allowed']:break
else:raise SystemExit('Ten reservation refusals')
payload={}
for name in ['build.py','native.py','capped.py','capped-template.py','reservation.py','rustc-diagnostics.py','r1-devnet.template.json','fixture-control-pins.json']:
 payload[name]=(P/name).read_text().replace(OLD,D)
payload['source-revision.txt']=REV+'\n'
payload['compare-fixtures.py']=(P/'compare-fixtures.py').read_text().replace(OLD,D).replace("r['passed']=r['passed'] and r['literal_raw_result_json_passed']","# D328: seconds excluded from deterministic comparison").replace("Literal result.json bytes required by D325; seconds difference is a stop unless lead clarifies otherwise.","D328 deterministic criterion; elapsed seconds excluded.")
remote(f'''from pathlib import Path
import os,json,hashlib
D=Path({D!r});payload={payload!r}
for n,s in payload.items():(D/n).write_text(s)
os.chmod(D/'rustc-diagnostics.py',0o755)
(D/'source').mkdir()
(D/'runner-pins.json').write_text(json.dumps({{n:hashlib.sha256(s.encode()).hexdigest() for n,s in payload.items()}},indent=2))
''')
paths=['Cargo.toml','Cargo.lock','.cargo','crates','programs','audit','xtask','tools','docs/research/v8-r0-zk-20261009/refine','docs/research/v8-r0-zk-20261009/c3','docs/research/v8-r0-zk-20261009/z4']
a=subprocess.Popen(['git','archive',REV,*paths],stdout=subprocess.PIPE)
r=subprocess.run(['ssh',HOST,f'tar xf - -C {D}/source'],stdin=a.stdout);a.stdout.close();assert r.returncode==0 and a.wait()==0
rows=json.loads(remote(f'''from pathlib import Path
import json,hashlib
D=Path({D!r})/'source';print(json.dumps({{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file()}}))
'''))
p=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
bad=[]
for path,h in rows.items():
 p.stdin.write((REV+':'+path+'\n').encode());p.stdin.flush();head=p.stdout.readline().split();assert head[1]==b'blob';data=p.stdout.read(int(head[2]));assert p.stdout.read(1)==b'\n'
 if hashlib.sha256(data).hexdigest()!=h:bad.append(path)
p.stdin.close();p.wait()
(E/'source-identity.json').write_text(json.dumps(dict(revision=REV,files=rows,disagreements=bad,passed=not bad),indent=2)+'\n');assert not bad
print('PREPARED',len(rows),flush=True)
