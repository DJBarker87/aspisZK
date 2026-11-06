"""Read-only final cache/export retention inventory; no scope or build."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,lzma,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-ledger19-20261108')
c=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKN_20261108')
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
seed=json.loads(lzma.decompress((b/'NKN_CACHE_IMPORTS.json.xz').read_bytes()))
for r in seed['files']:assert h(Path(r['destination']))==r['sha256']
ex=json.loads((b/'NKN_EXPORT.json').read_text())
for r in ex['files']:assert h(Path(r['path']))==r['sha256']
files=[p for p in b.rglob('*')if p.is_file()];cache=[p for p in c.rglob('*')if p.is_file()]
print(json.dumps(dict(status='PASS',seed_files=len(seed['files']),exports=len(ex['files']),workspace_bytes=sum(p.stat().st_size for p in files),cache_bytes=sum(p.stat().st_size for p in cache),host_disk=shutil.disk_usage(b)._asdict(),TMPDIR_retained=str(b/'NKN_tmp'),cache_retained=str(c),deleted_paths=[],read_only=True)))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 with (E/'NKN_RETENTION_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode==255 and retry<10:time.sleep(60);continue
 assert r.returncode==0,r.stderr
 x=json.loads(r.stdout);assert x['host_disk']['free']>=40_000_000_000
 (E/'NKN_RETENTION.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x));break
