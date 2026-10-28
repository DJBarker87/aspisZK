from NCG_host import *
r=py(f'''from pathlib import Path
import hashlib,json,os
b=Path({B!r});tools={{}}
for name,path in [('cargo-kani','/home/dombarker/.cargo/bin/cargo-kani'),('kani-driver','/home/dombarker/.kani/kani-0.67.0/bin/kani-driver'),('cbmc','/home/dombarker/.kani/kani-0.67.0/bin/cbmc'),('lean','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')]:
 p=Path(path);tools[name]=dict(path=str(p),resolved=str(p.resolve()),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
# Retain compiled proof artifacts by hash and size only before removing the target tree.
artifacts=[]
root=b/'NCG_target'
if root.exists():
 for p in root.rglob('*'):
  if p.is_file() and p.suffix in ['.out','.goto','.symtab']:
   artifacts.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(dict(tools=tools,compiled_artifacts=artifacts,kind='read-only terminal inventory; no proof replay'),indent=2))
''');assert r.returncode==0,r.stderr
(E/'NCG_TOOL_ARTIFACT_PIN.json').write_text(r.stdout)
