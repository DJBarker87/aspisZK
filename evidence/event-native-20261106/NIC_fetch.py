from pathlib import Path
import subprocess,json,base64,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-event-native-20261106'
names=['NIC_CLOSURE_PINS.json.xz','NIC_CLOSURE_PINS.json.sha256','NIC_EXPORT.json','NIC_RESTORE_PATHS.json','NIC_TOOLS.json','NIC_CLEANUP.json']
code="""from pathlib import Path
import json,base64
b=Path(%r);out={}
for n in %r:
 p=b/n
 if p.exists():out[n]=base64.b64encode(p.read_bytes()).decode()
for n in ['Cargo.toml','rust-toolchain.toml','.cargo/config.toml']:
 p=b/'NIC_src'/n
 if p.exists():out['NIC_ROOT_'+n.replace('/','_')+'.txt']=base64.b64encode(p.read_bytes()).decode()
print(json.dumps(out))
"""%(B,names)
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 with (E/'NIC_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(stage='fetch',retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
for n,raw in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(raw))
print('Fetched',len(json.loads(r.stdout)),'evidence files')
