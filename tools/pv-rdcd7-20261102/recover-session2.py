from pathlib import Path
import subprocess,json,hashlib,datetime
E=Path('evidence/pv-rdcd7-20261102');D='/home/dombarker/project-offloads/codex-pv-rdcd7-20261102'
code='''from pathlib import Path
import json,subprocess
D=Path("'''+D+'''")
a={p.name:{n:(p/n).read_text() if (p/n).exists() else None for n in ['time.log','output.log','admission-barrier.json']} for p in D.iterdir() if p.is_dir() and (p.name.startswith('lean-907') or p.name.startswith('N908'))}
print(json.dumps(dict(attempts=a,processes=subprocess.check_output(['ps','-eo','pid,ppid,etimes,args'],text=True))))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);results=[]
for name,files in sorted(j['attempts'].items()):
 p=E/name/'receipt.json';assert p.exists(),('recover missing receipt',name)
 rec=json.loads(p.read_text())
 for n,data in files.items():assert data==(E/name/n).read_text(),(name,n,'host/local difference')
 results.append(dict(name=name,exit=rec['exit'],receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
active=[l for l in j['processes'].splitlines() if D in l and 'python3 -' not in l]
assert not active,active
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),host=D,host_local_files_identical=True,attempts=results,active_task_processes=active,lean_spent=14,native_spent=2,lean_remaining=46,native_remaining=8,next_ordinary_lean_id=90714,next_native_id='N90802',reserved_audit_ids=[90797,90798,90799],basis='all host attempt directories reconciled; no live task process; never reuse spent IDs')
(E/'RESUME-SESSION2.json').write_text(json.dumps(out,indent=2)+'\n')
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
print(json.dumps(out,indent=2))
