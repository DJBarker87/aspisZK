#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
O=H/'export';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for p in (H/'receipts').glob('*/*'):
 if p.suffix in ['.json','.log']:copy(p,p.relative_to(H))
for p in H.glob('*-admission.json'):copy(p,p.name)
for p in H.glob('*-input.json'):copy(p,p.name)
llbc=[]
for folder in sorted([p for p in H.iterdir() if p.is_dir() and (p.name.startswith('caller-') or p.name.startswith('prepared-'))]):
 for p in folder.glob('*-input.json'):copy(p,p.relative_to(H))
 for p in folder.glob('*.llbc'):
  x=json.loads(p.read_text());llbc.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size,has_errors=x.get('has_errors')))
 if folder.name=='caller-v4':
  for p in (folder/'generated').rglob('*'):
   if p.is_file():copy(p,str(p.relative_to(H))+'.txt')
(O/'llbc-pins.json').write_text(json.dumps(llbc,indent=2)+'\n')
copy(H/'crate/Cargo.lock','sdk/Cargo.lock')
sdkroot=Path('/home/dombarker/.cargo/registry/src')
files=[]
for package in ['solana-account-info-2.3.0','solana-program-error-2.2.2','solana-pubkey-2.4.0']:
 for p in sdkroot.glob('*/'+package+'/src/lib.rs'):
  copy(p,'sdk/'+package+'/lib.rs');files.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size,retained='sdk/'+package+'/lib.rs'))
versions={}
for tool in [['/home/dombarker/.cargo/bin/cargo','kani','--version'],['/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler','--version']]:
 r=subprocess.run(tool,text=True,capture_output=True);versions[' '.join(tool)]=dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr)
(O/'sdk-pins.json').write_text(json.dumps(dict(source_files=files,versions=versions),indent=2)+'\n')
print('source-only export',O)
