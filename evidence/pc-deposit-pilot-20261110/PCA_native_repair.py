from pathlib import Path
import json,lzma,base64,tomllib,posixpath,subprocess,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
x=json.loads(lzma.decompress((E/'PCA_NATIVE_FROZEN_INPUTS.json.xz').read_bytes()));files={n:base64.b64decode(v) for n,v in x.items()};new={};pending=[n for n in files if n.endswith('Cargo.toml')];seen=set()
def scan(d):
 if isinstance(d,dict):
  if isinstance(d.get('path'),str):yield d['path']
  for v in d.values():yield from scan(v)
 elif isinstance(d,list):
  for v in d:yield from scan(v)
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n)
 for rel in scan(tomllib.loads(files[n].decode())):
  p=posixpath.normpath(posixpath.join(posixpath.dirname(n),rel));assert not p.startswith(('../','/')),p
  manifest=p+'/Cargo.toml'
  if manifest in files:continue
  r=subprocess.run(['git','cat-file','-e',rev+':'+manifest],capture_output=True)
  if r.returncode:continue # A package metadata file path is not a Cargo dependency.
  paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'--',p],text=True).splitlines()
  for z in paths:
   if z.endswith('.rs') or z.endswith('Cargo.toml'):
    b=subprocess.check_output(['git','show',rev+':'+z]);files[z]=b;new['PCA_src/'+z]=b.decode()
    if z.endswith('Cargo.toml'):pending.append(z)
pins={n:hashlib.sha256(b).hexdigest() for n,b in files.items()};(E/'PCA_NATIVE_FROZEN_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');new['PCA_NATIVE_FROZEN_PINS.json']=(E/'PCA_NATIVE_FROZEN_PINS.json').read_text()
(E/'PCA_NATIVE_REPAIR_FILES.json').write_text(json.dumps(new,indent=1)+'\n')
raw=json.dumps({n:base64.b64encode(b).decode() for n,b in files.items()}).encode();(E/'PCA_NATIVE_FROZEN_INPUTS.json.xz').write_bytes(lzma.compress(raw));(E/'PCA_NATIVE_FROZEN_INPUTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print('Owned scratch repair: '+str(len(new)-1)+' frozen path-dependency source files added; graph validation unchanged.')
