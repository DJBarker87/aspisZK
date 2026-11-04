"""Admitted transport of this task's committed inputs to its private host dir."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101';D='/home/dombarker/project-offloads/codex-pv-rdcd5-20261101';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
label,*paths=sys.argv[1:];assert label.replace('-','').isalnum() and paths
if (E/'last-launch.json').exists():
 remaining=180-(time.time()-json.load(open(E/'last-launch.json'))['epoch'])
 if remaining>0:print('Cooldown before transport:',remaining);sys.exit(78)
out=E/('stage-'+label);out.mkdir(exist_ok=True)
r=subprocess.run(['ssh',H,f'mkdir -p {D}/stage-{label}; python3 {G}/reservation.py {D}/stage-{label}/admission.json > {D}/stage-{label}/reservation.log 2>&1'],capture_output=True,text=True)
for n in ['admission.json','reservation.log']:
 q=subprocess.run(['ssh',H,f'cat {D}/stage-{label}/{n}'],capture_output=True,text=True);assert q.returncode==0,q.stderr;(out/n).write_text(q.stdout)
a=json.load(open(out/'admission.json'));assert r.returncode==0 and a['allowed'] is True,(r.returncode,a)
manifest=[]
for name in paths:
 p=R/name;b=p.read_bytes();assert b==subprocess.check_output(['git','show','HEAD:'+name],cwd=R),('uncommitted input',name)
 subprocess.run(['scp','-q',str(p),H+':'+D+'/'+p.name],check=True)
 manifest.append(dict(local=name,host=D+'/'+p.name,sha256=hashlib.sha256(b).hexdigest()))
(out/'transport.json').write_text(json.dumps(manifest,indent=2)+'\n');print('Admitted upload:',len(paths),'committed inputs')
