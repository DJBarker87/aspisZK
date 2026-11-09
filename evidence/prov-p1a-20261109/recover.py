import subprocess,json,base64,lzma,hashlib,sys,shlex
from pathlib import Path
a=sys.argv[1];B='/home/dombarker/project-offloads/codex-pc-prov-p1a-20261109';E=Path('.')
code=f'''from pathlib import Path
import json,base64
b=Path({B!r});a={a!r};names=[p for p in (b/a).rglob('*') if p.is_file()]+[b/(a+'.json')]+[p for p in (b/(a+'_emitted')).rglob('*') if p.is_file()]
names=[p for p in names if p.suffix!='.llbc' and p.name not in ('metadata.json','metadata.stdout')]
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in names}}))'''
r=subprocess.run(['ssh','-o','ConnectTimeout=20','-o','ServerAliveInterval=15','dombarker@100.108.41.90','timeout 300 python3'],input=code,capture_output=True,text=True)
assert r.returncode==0,r.stderr
for n,v in json.loads(r.stdout).items():
    raw=base64.b64decode(v);p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
    if (len(raw)>1_000_000 or n.endswith(('stdout.log','time.log','charon.time','aeneas.time','metadata.stderr'))) and not n.endswith('.xz'):
        p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
    else:p.write_bytes(raw)
print('recovered',a)
