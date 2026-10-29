from NEF_host import *
import hashlib
admit('NEF_KMX001')
s=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text();assert hashlib.sha256(s.encode()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
# The official patch contains only new files. Preserve their bytes exactly.
files={};name=None;buf=[]
for l in s.splitlines(True):
 if l.startswith('diff --git'):
  if name:files[name]=''.join(buf)
  name=None;buf=[]
 elif l.startswith('+++ b/'):name=l[6:].strip()
 elif name and l.startswith('+') and not l.startswith('+++'):buf.append(l[1:])
if name:files[name]=''.join(buf)
assert set(files)=={'KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean'}
files['crates/aspis-r1-cost-probe/src/NEF_native.rs']=(E/'NEF_combined.rs.txt').read_text()+'\n'+(E/'NEF_extra_harness.rs.txt').read_text()
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r})/'NEF_src';files=json.loads({json.dumps(files)!r})
for n,t in files.items():(b/n).write_text(t)
p=b/'crates/aspis-r1-cost-probe/src/lib.rs'
s=p.read_text()
if 'feature(allocator_api)' not in s:s='#![cfg_attr(kani,feature(allocator_api))]\\n'+s;p.write_text(s)
print(json.dumps({{n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in files}}))
''');assert r.returncode==0,r.stderr
pins=json.loads((E/'NEF_SCRATCH_PINS.json').read_text());pins.update(json.loads(r.stdout));(E/'NEF_SCRATCH_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(E/'NEF_KMX_PIN.json').write_text(json.dumps(dict(patch_sha256=hashlib.sha256(s.encode()).hexdigest(),files=json.loads(r.stdout)),indent=2)+'\n')
