from pathlib import Path
import subprocess,json,base64,hashlib
E=Path(__file__).resolve().parent;D=E/'PCB_RAW_FINAL';D.mkdir(exist_ok=True)
code="""from pathlib import Path
import json,lzma,base64
b=Path('/home/dombarker/project-offloads/codex-pc-helpers1-20261110');print(json.dumps({p.name:base64.b64encode(lzma.compress(p.read_bytes())).decode() for p in b.glob('PCB_NEP_*') if p.is_file()}))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():
 raw=base64.b64decode(s);(D/(n+'.xz')).write_bytes(raw);(D/(n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
print('Collected final raw graphs as compressed artifacts: '+str(len(json.loads(r.stdout))))
