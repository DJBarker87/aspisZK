from pathlib import Path
import json,hashlib,shutil,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');rows=[]
assert D.resolve()==D
for name in ['lean-objects','target-weights']:
 p=D/name
 assert p.is_dir() and not p.is_symlink()
 files=[f for f in p.rglob('*') if f.is_file()]
 # These directories were created by this job and contain only compiler/Cargo
 # artifacts. No wallet/account key was created or used by any fixture.
 if name=='lean-objects':assert all(f.suffix in ['.olean','.ilean','.trace','.private','.server','.ir'] or '.olean.' in f.name for f in files)
 binaries=[]
 if name=='target-weights':
  for n in ['fixture','v239','pairs']:
   b=p/'release'/n
   if b.exists():binaries.append(dict(path=str(b),sha256=hashlib.sha256(b.read_bytes()).hexdigest(),bytes=b.stat().st_size))
 row=dict(path=str(p),files=len(files),bytes=sum(f.stat().st_size for f in files),binary_hashes=binaries)
 shutil.rmtree(p);row['removed']=not p.exists();rows.append(row)
r=subprocess.run(['/home/dombarker/.cargo/bin/rustc','+1.94.1','--version','--verbose'],capture_output=True,text=True);assert r.returncode==0
j=dict(removed=rows,retained='all sources, receipts, source/LLVM excerpts and manifests, complete dependency fingerprints; every other job directory untouched',wallet_or_account_keys_touched=False,rustc=r.stdout)
(D/'cleanup.json').write_text(json.dumps(j,indent=2));print(json.dumps(j,indent=2))
