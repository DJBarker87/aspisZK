#!/usr/bin/env python3
"""Source-only MIR diagnostics. Failed translations are not proof evidence."""
from pathlib import Path
import hashlib,json,shutil,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');base=H/'s1-native-mir-20261024';out=base/'source-only-packet';out.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for stage in ['promoted','elaborated','optimized']:
 for phase in ['charon','aeneas']:
  name='s1-original-mir-'+stage+'-'+phase+'-v1';root=base/name
  for p in root.rglob('*'):
   if p.is_file() and p.suffix in ['.json','.log']:copy(p,out/'attempts'/name/p.relative_to(root))
 llbc=base/stage/'OriginalClaim.llbc';raw=json.loads(llbc.read_text());assert not raw['has_errors']
 (out/(stage+'-llbc-pin.json')).write_text(json.dumps(dict(sha256=hashlib.sha256(llbc.read_bytes()).hexdigest(),has_errors=raw['has_errors'],bytes=llbc.stat().st_size,qualification='Hash only; no LLBC or binaries distributed.'),indent=2)+'\n')
 for p in (base/stage/'generated').rglob('*'):
  if p.is_file() and p.suffix in ['.lean','.json']:copy(p,out/'excluded-generated'/stage/p.relative_to(base/stage/'generated'))
source=base/'promoted/input'
for p in source.rglob('*'):
 if p.is_file() and p.suffix in ['.rs','.json','.toml','.lock','.md','.txt']:copy(p,out/'input'/p.relative_to(source))
copy(H/'s1-native-mir-runner-20261024.py',out/'runner.py')
files={str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest() for p in out.rglob('*') if p.is_file()}
(out/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='All three source-preserving MIR alternatives have valid Charon LLBC and failed Aeneas translation. No original claim equivalence, Lean closure, binary or accepted proof artifact.'),indent=2)+'\n')
archive=base/'source-only-packet.tar.gz'
with tarfile.open(archive,'w:gz') as tar:
 for p in out.rglob('*'):
  if p.is_file():tar.add(p,arcname=p.relative_to(out))
print(json.dumps(dict(files=len(files),archive=str(archive))))
