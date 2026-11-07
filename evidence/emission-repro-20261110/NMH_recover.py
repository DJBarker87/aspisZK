#!/usr/bin/env python3
"""Read-only recovery after submitted scopes; never launches or resubmits tools."""
from pathlib import Path
import subprocess,json,lzma,hashlib,base64,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-emission-repro-20261110'
def main():
 code='''from pathlib import Path
import json,hashlib,base64,lzma,os
b=Path(%r);w=b/'NMH_workspace';manifest=json.loads((b/'NMH_STAGING_MANIFEST.json').read_text())
drift=[n for n,v in manifest['files'].items() if not (w/n).exists() or hashlib.sha256((w/n).read_bytes()).hexdigest()!=v['sha256']]
files={}
for p in b.glob('NMH_E*_emitted/*.llbc'):
 raw=p.read_bytes();files[str(p.relative_to(b))+'.xz']=base64.b64encode(lzma.compress(raw,preset=6)).decode();files[str(p.relative_to(b))+'.sha256']=base64.b64encode((hashlib.sha256(raw).hexdigest()+'\\n').encode()).decode()
for p in b.glob('NMH_E*/NMH_POSTCHECK.json'):files[str(p.relative_to(b))]=base64.b64encode(p.read_bytes()).decode()
active=[]
for proc in Path('/proc').glob('[0-9]*'):
 try:
  cwd=os.readlink(proc/'cwd')
  if cwd==str(b) or cwd.startswith(str(b)+'/'):active.append(dict(pid=int(proc.name),comm=(proc/'comm').read_text().strip()))
 except (FileNotFoundError,PermissionError,ProcessLookupError):pass
post=dict(owned_processes=active,source_drift=drift,lock_sha256=hashlib.sha256((w/'Cargo.lock').read_bytes()).hexdigest(),expected_lock_sha256=manifest['files']['Cargo.lock']['sha256'],owned_bytes=sum(os.stat(os.path.join(d,n)).st_size for d,ds,ns in os.walk(b) for n in ns),free_bytes=__import__('shutil').disk_usage(b).free)
print(json.dumps(dict(files=files,postcheck=post)))
'''%B
 for n in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
  if r.returncode!=255:break
  with (E/'NMH_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(step='read-only final recovery',retry=n,exit=255))+'\n')
  if n<10:time.sleep(60)
 assert r.returncode==0,r.stderr
 d=json.loads(r.stdout)
 for name,b in d['files'].items():
  p=E/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(b))
 (E/'NMH_HOST_POSTCHECK.json').write_text(json.dumps(d['postcheck'],indent=2)+'\n')
 assert not d['postcheck']['source_drift'] and d['postcheck']['lock_sha256']==d['postcheck']['expected_lock_sha256'],'STOP frozen source or lock drift'
 assert d['postcheck']['owned_bytes']<30_000_000_000
 print(json.dumps(dict(recovered_files=len(d['files']),postcheck=d['postcheck'])))
if __name__=='__main__':main()
