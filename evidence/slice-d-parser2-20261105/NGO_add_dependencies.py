from pathlib import Path
import subprocess,tomllib,posixpath,json,base64,hashlib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
pins=json.loads((E/'NGO_SOURCE_PINS.json').read_text());queue=[''];seen=set();roots=set()
def read(n):return subprocess.check_output(['git','show',F+':'+n])
def paths(d,base):
 if isinstance(d,dict):
  if isinstance(d.get('path'),str):
   p=posixpath.normpath(posixpath.join(base,d['path']))
   if subprocess.run(['git','cat-file','-e',F+':'+p+'/Cargo.toml'],capture_output=True).returncode==0:queue.append(p)
  for v in d.values():paths(v,base)
 elif isinstance(d,list):
  for v in d:paths(v,base)
while queue:
 root=queue.pop()
 if root in seen:continue
 seen.add(root);d=tomllib.loads(read(posixpath.join(root,'Cargo.toml')).decode());paths(d,root)
 queue += [posixpath.normpath(posixpath.join(root,p)) for p in d.get('workspace',{}).get('members',[]) if '*' not in p]
 if root and not root.startswith(('crates/','programs/')):roots.add(root)
roots.update(["tools/r1-builder-reference","docs/research/v8-r0-zk-20261009/refine/diffharness/tests"])
files={}
for root in sorted(roots):
 for n in subprocess.check_output(['git','ls-tree','-r','--name-only',F,root],text=True).splitlines():
  if n in pins:continue
  b=read(n);files[n]=base64.b64encode(b).decode();pins[n]=hashlib.sha256(b).hexdigest()
(E/'NGO_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1))
(E/'NGO_PATH_DEPENDENCIES.json').write_text(json.dumps(dict(roots=sorted(roots),files={n:v for n,v in pins.items() if not n.startswith(('crates/','programs/'))}),indent=1))
code='''from pathlib import Path
import json,base64,subprocess,sys
b=Path('/home/dombarker/project-offloads/codex-cx-slice-d-parser2-20261105')
p=b/'NGO_DEPENDENCIES-admission.json'
with (b/'NGO_DEPENDENCIES-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING',flush=True)
if r.returncode!=0 or not p.exists() or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
s=b/'NGO_src'
files=json.loads('''+repr(json.dumps(files))+''')
for n,v in files.items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NGO_DEPENDENCIES.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
print('Pinned and restored dependency roots:',sorted(roots),'new files:',len(files))
