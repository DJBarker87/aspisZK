"""Submit own new modules only; unchanged shared Env-J launcher and caps."""
from pathlib import Path
import json,sys,subprocess,hashlib,shlex,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb1-20261028';D='/home/dombarker/project-offloads/codex-pv-rdb1-20261028';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);m=sys.argv[2];assert 54700<=n<=54799 and m.startswith('R1Z/PV_RDB1_')
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');b=p.read_bytes();rel=str(p.relative_to(R));assert b==subprocess.check_output(['git','show','HEAD:'+rel])
assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',b.decode());assert not re.search(r'^import .*XR',b.decode(),re.M)
def ssh(c):return subprocess.run(['ssh',H,c],text=True,capture_output=True)
assert n < 54797 or any(x in m for x in ['Audit','Replay'])
# Cross-job receipt names as well as the global sent ledger. Only own new files are uploaded.
check='''from pathlib import Path
import re,json
B=Path('/home/dombarker/project-offloads');n=NUMBER
hits=[]
for p in B.glob('codex-pv-*'):
 for pattern in [str(n), 'runs/'+str(n), 'evidence/'+str(n), 'receipts/'+str(n), 'evidence/out-'+str(n)+'.log', 'lean/'+str(n), 'receipts/out-'+str(n)+'.log']:
  q=p/pattern
  if q.exists():hits.append(str(q))
s=B/'r1-privacy-build-integration-20261019/evidence/sent.txt'
for line in s.read_text().splitlines():
 if re.search(r' J '+str(n)+r' ',line):hits.append(line)
print(json.dumps(hits))
'''.replace('NUMBER',str(n))
r=ssh('python3 -c '+shlex.quote(check));assert r.returncode==0,r.stderr;hits=json.loads(r.stdout);assert not hits,hits
(E/f'{n}-id-check.json').write_text(r.stdout)
pre=ssh('cat '+D+'/preflight.json');assert pre.returncode==0 and json.loads(pre.stdout)['ok'];(E/'preflight.json').write_text(pre.stdout)
G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
r=ssh(f'python3 {G}/reservation.py {D}/lean-upload-{n}.json > {D}/lean-upload-{n}.log 2>&1');a=ssh(f'cat {D}/lean-upload-{n}.json');(E/f'{n}-admission.json').write_text(a.stdout)
assert r.returncode==0 and json.loads(a.stdout)['allowed'] is True,('refusal',r.returncode)
meta=dict(id=n,module=m,source_sha256=hashlib.sha256(b).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],text=True).strip(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),imports=re.findall(r'^import (\S+)',b.decode(),re.M),external_preflight='preflight.json')
own={}
def visit(k):
 if not k.startswith('R1Z.PV_RDB1_') or k in own:return
 path='docs/research/v8-r0-zk-20261009/lean/'+k.replace('.','/')+'.lean'
 data=subprocess.check_output(['git','show','HEAD:'+path]);root='/home/dombarker/project-offloads/aspis-joint-20261019'
 remote=root+'/sources/'+k.replace('.','/')+'.lean'
 q=ssh('sha256sum '+remote+' '+root+'/objects/'+k.replace('.','/')+'.olean');assert q.returncode==0,q.stderr
 lines=q.stdout.splitlines();assert lines[0].split()[0]==hashlib.sha256(data).hexdigest(),('import source mismatch',k)
 own[k]=dict(path=path,source_sha256=hashlib.sha256(data).hexdigest(),object_sha256=lines[1].split()[0],blob=subprocess.check_output(['git','rev-parse','HEAD:'+path],text=True).strip())
 for dep in re.findall(r'^import (\S+)',data.decode(),re.M):visit(dep)
for k in meta['imports']:visit(k)
meta['own_imports']=own
(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2))
subprocess.run(['scp','-q',str(p),H+':/home/dombarker/project-offloads/aspis-joint-20261019/sources/'+m+'.lean'],check=True)
fp=hashlib.sha256((E/'preflight.json').read_bytes()).hexdigest()
cmd=['/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh',str(n),m,'J','7000','8',fp]
r=ssh(shlex.join(cmd));(E/f'{n}-launcher.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr)
if r.returncode:sys.exit(r.returncode)
T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
for f in ['out-'+str(n)+'.log','time-'+str(n)+'.log','sha-'+str(n)+'.txt']:
 q=ssh('cat '+T+'/'+f);assert q.returncode==0,q.stderr;(E/f).write_text(q.stdout)
