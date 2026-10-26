"""Read-only input receipt for a direct invocation of an existing launcher.
This does not launch, cap, lock, monitor, or modify any build infrastructure.
"""
from pathlib import Path
import hashlib,json,re,sys
h=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/receipts')
h.mkdir(parents=True,exist_ok=True)
j=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
a=int(sys.argv[1]);module=sys.argv[2];revision=sys.argv[3]
assert 12000<=a<=12399 and module.startswith('R1Z/PDict_')
assert not (h/f'{a}-input.json').exists()
assert not Path(f'/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/out-{a}.log').exists()
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
roots=[j/'objects',*[Path(p) for p in env['LEAN_PATH'].split(':')]]
def imports(s):
 clean=[];depth=0;i=0
 while i<len(s):
  pair=s[i:i+2]
  if pair=='/-':depth+=1;i+=2;continue
  if depth and pair=='-/':depth-=1;i+=2;continue
  if depth:
   if s[i]=='\n':clean.append('\n')
   i+=1;continue
  if pair=='--':
   end=s.find('\n',i);i=len(s) if end<0 else end;continue
  clean.append(s[i]);i+=1
 return [m for line in ''.join(clean).splitlines() if line.startswith('import ') for m in line[7:].split()]
deps=[];seen=set()
def visit(name):
 if name in seen:return
 seen.add(name);rel=name.replace('.','/')
 obj=next((r/(rel+'.olean') for r in roots if (r/(rel+'.olean')).is_file()),None)
 assert obj,('missing dependency',name)
 src=j/'sources'/(rel+'.lean');children=imports(src.read_text()) if src.is_file() else []
 deps.append(dict(module=name,object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest(),resolved_object=str(obj),source_imports=children))
 for child in children:visit(child)
src=j/'sources'/(module+'.lean');s=src.read_text()
for name in imports(s):visit(name)
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
(h/f'{a}.lean.txt').write_text(s)
(h/f'{a}-input.json').write_text(json.dumps(dict(module=module,attempt=a,source_revision=revision,source_sha256=hashlib.sha256(s.encode()).hexdigest(),source_path=str(src),dependencies=deps,deps_fingerprint=fp,launcher='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/'+'native-drop'+'/run-joint.sh',limits=dict(lean_memory_mb=7000,memory_high='5G',memory_max='7G',swap_max=0,tasks_max=64)),indent=2)+'\n')
print(fp)
