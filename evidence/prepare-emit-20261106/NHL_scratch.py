"""Reproduce source pins without changing repository source or shared caches.
The initial materialization used per-file git show; this version uses cat-file
batch for identical inputs/validation and avoids thousands of git processes.
"""
from pathlib import Path
import subprocess,json,hashlib,base64
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
names=[x['path'] for x in json.loads((E/'NHL_SOURCE_PINS.json').read_text())]
expected={x['path']:x for x in json.loads((E/'NHL_SOURCE_PINS.json').read_text())}
p=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
payload={}
for n in names:
 p.stdin.write((rev+':'+n+'\n').encode());p.stdin.flush()
 header=p.stdout.readline().split();size=int(header[2]);raw=p.stdout.read(size);assert p.stdout.read(1)==b'\n'
 assert hashlib.sha256(raw).hexdigest()==expected[n]['sha256']
 payload[n]=base64.b64encode(raw).decode()
p.stdin.close();assert p.wait()==0
# Source bytes are already retained in the pinned Git tree, never as another corpus.
code='''from pathlib import Path
import json,base64,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-prepare-emit-20261106');s=b/'NHL_src'
for n,t in json.loads(INPUT).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(t))
'''.replace('INPUT',repr(json.dumps(payload)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True);raise SystemExit(r.returncode)
