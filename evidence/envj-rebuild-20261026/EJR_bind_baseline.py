"""Bind intact whole library namespaces inside authorized output directories."""
from pathlib import Path
import json,os,hashlib
B=Path('/home/dombarker/project-offloads');T=B/'aspis-fs-generic-20261006/evidence';U=B/'codex-cx-import-union-20261022';J=B/'aspis-joint-20261019';env=json.loads((B/'r1-privacy-build-integration-20261019/env/J.json').read_text());bindings={}
core=Path(env['LEAN_SYSROOT'])/'lib/lean'
for name in ['Init','Lean','Std','Lake']:bindings[name]=core
for base in [Path(p) for p in env['LEAN_PATH'].split(':') if '/.lake/packages/' in p]:
 if not base.is_dir():continue
 for d in base.iterdir():
  if d.is_dir() and d.name not in ['lib','bin']:bindings[d.name]=base
bindings['Aeneas']=U/'retained-objects';bindings['AeneasMeta']=U/'retained-objects'
report=[]
for root in [J,U]:
 target=root/'objects';snap=root/'EJR_baseline_previous';snap.mkdir(exist_ok=True)
 for name,base in bindings.items():
  original=base/name;dest=target/name
  if not original.is_dir():continue
  if dest.is_symlink():
   if dest.resolve()==original.resolve():pass
   else:dest.unlink();dest.symlink_to(original.resolve(),target_is_directory=True)
  elif dest.exists():
   # Existing library views were generated symlinks, never proof output.
   assert all(p.is_symlink() or p.is_dir() for p in dest.rglob('*')),str(dest)
   assert not (snap/name).exists();os.rename(dest,snap/name);dest.symlink_to(original.resolve(),target_is_directory=True)
  else:dest.symlink_to(original.resolve(),target_is_directory=True)
  flat=[]
  for src in base.glob(name+'.*'):
   if not src.is_file() or not any(str(src).endswith(e) for e in ['.olean','.olean.private','.olean.server','.ir']):continue
   out=target/src.name
   if out.is_symlink():out.unlink()
   elif out.exists():raise RuntimeError('unexpected regular library root '+str(out))
   out.symlink_to(src.resolve());flat.append(dict(path=str(out),source=str(src.resolve()),sha256=hashlib.sha256(src.read_bytes()).hexdigest()))
  report.append(dict(workspace=str(root),namespace=name,target=str(dest),source=str(original.resolve()),roots=flat))
(T/'EJR-namespace-bindings.json').write_text(json.dumps(report,indent=2)+'\n');print('bound',len(report),'whole package namespaces')
