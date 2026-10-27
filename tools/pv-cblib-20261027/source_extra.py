"""Read-only retrieval of additional Cargo.lock-pinned source files."""
from pathlib import Path
import subprocess,shlex,json,hashlib,tomllib
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027'
lock=tomllib.loads((root/'Cargo.lock').read_text())
files=[('generic-array','0.14.7','src/lib.rs'),('block-buffer','0.10.4','src/lib.rs'),('crypto-common','0.1.7','src/lib.rs'),('sha2','0.10.9','src/consts.rs'),('sha2','0.10.9','src/sha256.rs'),('sha2','0.10.9','src/sha256/x86.rs'),('sha2','0.10.9','src/sha256/soft.rs'),('sha2','0.10.9','Cargo.toml'),('cpufeatures','0.2.17','src/x86.rs')]
requests=[]
for crate,version,name in files:
 packages=[p for p in lock['package'] if p['name']==crate and p['version']==version];assert len(packages)==1
 requests.append((crate,version,name,packages[0]['checksum']))
code='''from pathlib import Path
import json,hashlib,tarfile
r={}
for crate,version,name,checksum in %r:
 p=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')/f'{crate}-{version}'/name
 archive=Path('/home/dombarker/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f')/f'{crate}-{version}.crate'
 assert hashlib.sha256(archive.read_bytes()).hexdigest()==checksum
 b=p.read_bytes();sha=hashlib.sha256(b).hexdigest()
 with tarfile.open(archive) as package:assert package.extractfile(f'{crate}-{version}/{name}').read()==b
 r[f'{crate}-{version}__{name.replace("/","__")}']={'crate':crate,'version':version,'path':str(p),'cargo_checksum':checksum,'sha256':sha,'body':b.decode()}
print(json.dumps(r))'''%requests
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True)
assert p.returncode==0,p.stderr
rows=json.loads(p.stdout)
for name,row in rows.items():
 dest=out/'source'/name;dest.write_text(row.pop('body'));assert hashlib.sha256(dest.read_bytes()).hexdigest()==row['sha256']
(out/'resume-backend-sources.json').write_text(json.dumps(rows,indent=2)+'\n');print({k:v['sha256'] for k,v in rows.items()})
