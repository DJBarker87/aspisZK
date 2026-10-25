"""Local source/hash/AST audit and literal package bootstrap bundling only."""
import ast
import difflib
import hashlib
import json
from pathlib import Path
import sys
H=Path(__file__).resolve().parent;O=H.parents[1]/'evidence/sbf-finite-probe-20261025'
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def save(p,v):
 b=(json.dumps(v,indent=2,sort_keys=True)+'\n').encode();assert len(b)<5_000_000;p.write_bytes(b)
def definitions(s):
 t=ast.parse(s);result={}
 for n in t.body:
  if isinstance(n,(ast.FunctionDef,ast.ClassDef)):
   if isinstance(n,ast.ClassDef):
    for m in n.body:
     if isinstance(m,ast.FunctionDef):result[n.name+'.'+m.name]=ast.get_source_segment(s,m)
   else:result[n.name]=ast.get_source_segment(s,n)
 return result
records={};patches=[]
# Source9f50 lineage is independently assessed against the final implementation.
for origin,new in [('SbfLinux_abi.py','SbfFiniteLinux_abi.py'),('SbfLinux_backend.py','SbfFinite_backend_candidate.py'),('SbfLinux_capture.py','SbfFiniteLinux_capture.py')]:
 p=O/('SbfFinite-source9f50-'+origin+'.txt')
 raw=p.read_text();renamed=raw.replace('SbfLinux','SbfFiniteLinux').replace('SbfSeal','SbfFinite')
 target=(H/new).read_text();a=definitions(renamed);b=definitions(target)
 records['9f50:'+origin]=dict(source=pin(raw.encode()),renamed=pin(renamed.encode()),target=pin(target.encode()),renames=[['SbfLinux','SbfFiniteLinux'],['SbfSeal','SbfFinite']],unchanged={k:pin(a[k].encode()) for k in a.keys()&b.keys() if a[k]==b[k]},complete_changed_statements={k:dict(before=a.get(k),after=b.get(k)) for k in a.keys()|b.keys() if a.get(k)!=b.get(k)})
 patches.extend(difflib.unified_diff(renamed.splitlines(True),target.splitlines(True),fromfile='9f50:'+origin,tofile=new))
for p in sorted(O.glob('*.baseline.txt')):
 n=p.name.removesuffix('.baseline.txt');before=p.read_text();after=(H/n).read_text()
 if n.endswith('.py'):
  a=definitions(before);b=definitions(after);unchanged={};changed={}
  for k in sorted(set(a)|set(b)):
   if a.get(k)==b.get(k):unchanged[k]=dict(byte_pin=pin(a[k].encode()),ast_pin=pin(ast.dump(ast.parse(a[k]),include_attributes=False).encode()))
   else:changed[k]=dict(before=a.get(k),after=b.get(k))
  records[n]=dict(before=pin(before.encode()),after=pin(after.encode()),unchanged=unchanged,complete_changed_statements=changed)
 else:records[n]=dict(before=pin(before.encode()),after=pin(after.encode()),exact_bytes=before==after)
 patches.extend(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile=n+'.baseline',tofile=n))
(O/'SbfFinite-delta.patch.txt').write_text(''.join(patches))
save(O/'SbfFinite-statements-and-identities.json',records)
# Finite package includes only concrete operative modules and fixed reviewed data.
names=['SbfFinite_fixed.py','SbfFinite_validate.py','SbfFiniteLinux_capture.py','SbfFiniteLinux_abi.py',
 'SbfFiniteLinux_backend.py','SbfFinite_backend_candidate.py','SbfFinite_continue.py','SbfFinite_observe.py',
 'SbfFinite_process.py','SbfFinite_package.py','SbfFiniteRss_adapter.py','SbfFiniteRss_guard.py',
 'SbfFiniteRss_sources.py','SbfFiniteRss_reviewed.json','SbfFinite_entry.py','SbfFinite_user_entry.py']
launcher=pin((H/'SbfFinite_root_launcher.sh.txt').read_bytes())
(H/'SbfFinite_launcher_pin.py').write_text("if __name__ == '__main__':\n    raise SystemExit('SbfFinite SOURCE ONLY: disabled before imports')\nLAUNCHER_PIN = "+repr(launcher)+'\n')
names.append('SbfFinite_launcher_pin.py')
files={n:pin((H/n).read_bytes()) for n in names}
(H/'SbfFinite_package_pins.py').write_text("if __name__ == '__main__':\n    raise SystemExit('SbfFinite SOURCE ONLY: disabled before imports')\n\"\"\"External bootstrap pins this file; it cannot self-certify.\"\"\"\nFILES = "+repr(files)+'\n')
names.append('SbfFinite_package_pins.py')
cat=[dict(name=n,pin=dict(pin((H/n).read_bytes()),mode=0o444),payload=(H/n).read_bytes()) for n in names]
(H/'SbfFinite_inventory.py').write_text("if __name__ == '__main__':\n    raise SystemExit('SbfFinite SOURCE ONLY: disabled before imports')\n\"\"\"Externally reviewed bootstrap payload; never adopted from staging.\"\"\"\nPACKAGE_CATALOG = "+repr(cat)+'\n')
save(O/'SbfFinite-installation.json',dict(schema='SbfFinite-installation-source-v1',
 package='/opt/aspis/SbfFinite-20261025-v1',root='/var/lib/SbfFinite-20261025-v1',
 package_files={n:dict(pin((H/n).read_bytes()),mode=0o444) for n in names},
 proposed_external_launcher=dict(path='/usr/local/libexec/SbfFinite-20261025-tiny-root',mode=0o555,**launcher),
 launcher_install='not installed by this finite installer; separate future lead-reviewed administrative publication, no sudoers grant',
 bootstrap={n:pin((H/n).read_bytes()) for n in ['SbfFinite_inventory.py','SbfFinite_install.py','SbfFinite_install_entry.py']},
 bootstrap_boundary='External exact bytes/interpreter/source-loader review required; selfpin does not authenticate itself',
 runtime_rows=92,runtime_copied_bytes=35655597,
 no_install=True,no_native=True,axioms='N/A'))
print('source statements/deltas sealed; fixed package literal payload generated')
