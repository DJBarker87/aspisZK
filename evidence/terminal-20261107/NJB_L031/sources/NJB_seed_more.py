from pathlib import Path
import json,hashlib,shutil,lzma,base64
b=Path(__file__).resolve().parent;c=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJB_20261107');records=[];missing=[]
specs=[('NFQ','/home/dombarker/project-offloads/codex-cx-slice-d-define-cache-20261104/NFQ_exports_20261104','NFQ_PreparedMultiplier.olean'),('NFS','/home/dombarker/project-offloads/codex-cx-slice-q-accum-cache-20261104/NFS_exports_20261104','NFS_QueryLoopRoot.olean'),('NFN','/home/dombarker/project-offloads/codex-cx-slice-q-phase-cache-20261104/NFN_exports_20261104','NFN_GeometryPart03.olean'),('NFM','/home/dombarker/project-offloads/codex-cx-slice-q-mul9-cache-20261104/NFM_exports_20261104','NFM_Packet.olean'),('leaf','/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027',''),('pilot','/home/dombarker/project-offloads/codex-cx-cpilot-cache-20261028','')]
for tag,root,name in specs:
 root=Path(root)
 if not root.exists():missing.append(str(root));continue
 files=sorted(root.glob('*.olean'));p=root/name if name and(root/name).is_file()else next(iter(files),None)
 if p is None:missing.append(str(root)+'/*.olean');continue
 for src in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not src.is_file():continue
  dest=c/('NJB_'+tag+'_seed')/src.name;dest.parent.mkdir(exist_ok=True)
  raw=src.read_bytes();h=hashlib.sha256(raw).hexdigest()
  if dest.exists():assert dest.read_bytes()==raw
  else:shutil.copy2(src,dest)
  records.append(dict(source=str(src),destination=str(dest),sha256=h,bytes=len(raw)))
# Preserve the failing extraction input once as compressed evidence, not a new extraction.
p=b/'NJB_emitted/NJB_terminal.llbc';raw=p.read_bytes();compressed=lzma.compress(raw,preset=6)
(b/'NJB_LLBC.xz.b64.txt').write_text(base64.b64encode(compressed).decode());(b/'NJB_LLBC.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
removed=[]
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in (b/'NJB_tmp').rglob(pattern):
  if p.is_file():removed.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
report=dict(files=records,bytes=sum(x['bytes']for x in records),missing=missing,order=[s[0]for s in specs],first_seed='NIU export (NJB_SEED)',llbc=dict(bytes=len(raw),xz_bytes=len(compressed),sha256=hashlib.sha256(raw).hexdigest()),removed_own_solver_temporary=removed,disk=shutil.disk_usage(b)._asdict())
(b/'NJB_EXTRA_SEED.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(dict(copied=len(records),bytes=report['bytes'],missing=len(missing),llbc_xz_bytes=len(compressed),removed_temp=len(removed))))
