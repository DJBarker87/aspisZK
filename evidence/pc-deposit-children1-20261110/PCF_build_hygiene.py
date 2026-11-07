"""Remove only terminal own Rust incremental build outputs; retain all proof inputs/caches."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
code='''from pathlib import Path
import json,hashlib,shutil
B=Path('/home/dombarker/project-offloads/codex-pc-deposit-children1-20261110')
# All native/extraction scopes are terminal. The only client is waiting on disk
# before PCF_L010; no Rust process is submitted by this client.
for n in ['PCF_K001','PCF_K002','PCF_K003','PCF_K004','PCF_K005','PCF_K007','PCF_K009','PCF_K010','PCF_E001','PCF_E002']:
 assert (B/n/'receipt.json').is_file(),n
p=B/'PCF_target/kani/x86_64-unknown-linux-gnu/debug/incremental'
assert str(p).startswith(str(B/'PCF_target')+'/')
files=[dict(path=str(f.relative_to(B)),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in p.rglob('*') if f.is_file()]
x=dict(action='Remove own terminal Rust incremental outputs only',retained='All source, receipts, lock/graph/feature pins, compiled dependencies and entire own retained PCF cache',files=files,bytes=sum(v['bytes'] for v in files),disk_before=shutil.disk_usage(B).free)
if p.exists():shutil.rmtree(p)
x['disk_after']=shutil.disk_usage(B).free;(B/'PCF_BUILD_HYGIENE.json').write_text(json.dumps(x,indent=1));print(json.dumps(x))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'PCF_BUILD_HYGIENE.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({k:v for k,v in x.items() if k!='files'}))
