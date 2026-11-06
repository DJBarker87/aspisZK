from pathlib import Path
import json,lzma,base64,tomllib,subprocess,posixpath,hashlib
E=Path(__file__).resolve().parent
rows=json.loads(lzma.decompress((E/'NLE_BASE.json.xz').read_bytes()))
revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
seen=set();added=[]
def add(path):
 if path+'/Cargo.toml' in rows:return
 check=subprocess.run(['git','cat-file','-e',revision+':'+path+'/Cargo.toml'],capture_output=True)
 assert check.returncode==0,path
 files=subprocess.check_output(['git','ls-tree','-r','--name-only',revision,'--',path],text=True).splitlines()
 for name in files:
  if name not in rows:
   rows[name]=base64.b64encode(subprocess.check_output(['git','show',revision+':'+name])).decode();added.append(name)
for member in tomllib.loads(base64.b64decode(rows['Cargo.toml']).decode())['workspace']['members']:add(member)
while True:
 manifests=[p for p in rows if p.endswith('Cargo.toml') and p not in seen]
 if not manifests:break
 for p in manifests:
  seen.add(p)
  def visit(x):
   if isinstance(x,dict):
    dep=x.get('path')
    if isinstance(dep,str) and not dep.endswith('.rs'):add(posixpath.normpath(posixpath.join(posixpath.dirname(p),dep)))
    for value in x.values():visit(value)
   elif isinstance(x,list):
    for value in x:visit(value)
  visit(tomllib.loads(base64.b64decode(rows[p]).decode()))
raw=json.dumps(rows,separators=(',',':')).encode()
(E/'NLE_BASE.json.xz').write_bytes(lzma.compress(raw,preset=6))
(E/'NLE_BASE.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'NLE_BASE_PINS.json').write_text(json.dumps({n:hashlib.sha256(base64.b64decode(b)).hexdigest() for n,b in rows.items()},indent=1))
print(json.dumps(dict(added=len(added),files=len(rows),bytes=len(raw),compressed=(E/'NLE_BASE.json.xz').stat().st_size)))
