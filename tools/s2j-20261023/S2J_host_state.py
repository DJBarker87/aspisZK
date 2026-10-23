from pathlib import Path
import hashlib,json,subprocess
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tools={}
for p in [Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')]:
 if p.exists():tools[str(p)]=dict(sha256=sha(p),bytes=p.stat().st_size)
lock=B/'S2J-cut1/Cargo.lock'
deps={}
if lock.exists():
 import tomllib
 for pkg in tomllib.loads(lock.read_text())['package']:
  for root in Path('/home/dombarker/.cargo/registry/src').glob('*'):
   folder=root/(pkg['name']+'-'+pkg['version'])
   if folder.exists():
    for p in sorted(folder.rglob('*')):
     if p.is_file():deps[str(p)]=dict(sha256=sha(p),bytes=p.stat().st_size)
artifacts={str(p.relative_to(B)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in (B/'kani-target').rglob('*') if p.is_file() and ('goto' in p.name or p.suffix=='.symtab')}
processes=subprocess.check_output(['ps','-eo','pid,args'],text=True).splitlines()
workers=[line for line in processes if str(B) in line and any(word in line for word in ['cargo-kani','cbmc','bin/lean '])]
(B/'S2J-host-state.json').write_text(json.dumps(dict(tools=tools,dependency_source_hashes=deps,artifacts=artifacts,worker_proof_processes=workers),indent=2)+'\n')
