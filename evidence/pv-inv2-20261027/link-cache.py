"""Read-only artifact references; no shared object/source is modified."""
import json,pathlib,hashlib
base=pathlib.Path('/home/dombarker/project-offloads/codex-pv-inv-20261027/inv2')
env=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'));rows=[]
for dst in (base/'objects/R1Z').rglob('*.olean'):
 if dst.is_symlink():dst.unlink()
for root in ['/home/dombarker/project-offloads/aspis-joint-20261019/objects']+env['LEAN_PATH'].split(':'):
 r=pathlib.Path(root)/'R1Z'
 if not r.exists():continue
 for p in r.rglob('*.olean'):
  if not p.is_file():continue
  dst=base/'objects/R1Z'/p.relative_to(r)
  if dst.is_symlink() and not dst.exists():dst.unlink()
  if not dst.exists():
   dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(p)
for dst in (base/'objects/R1Z').rglob('*.olean'):
 if dst.is_symlink() and dst.is_file():
  rows.append(dict(module='R1Z.'+str(dst.relative_to(base/'objects/R1Z')).replace('/','.')[:-6],target=str(dst.resolve()),sha256=hashlib.sha256(dst.read_bytes()).hexdigest()))
(base/'readonly-object-links.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows))
