"""Retain only this job's support objects; never write predecessor caches."""
from pathlib import Path
import json,hashlib,shutil,os
B=Path.cwd();dest=B/'NLD_exports_20261109';dest.mkdir(exist_ok=True)
skip=['NLD_Inspect','NLD_Driver','NLD_ProofDriver','NLD_STATEMENTS'];rows=[]
for p in sorted((B/'NLD_objects').rglob('*')):
 if not p.is_file()or any(p.name.startswith(n+'.')for n in skip):continue
 rel=p.relative_to(B/'NLD_objects');q=dest/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 rows.append(dict(path=str(p),retained=str(q),relative=str(rel),sha256=h,bytes=q.stat().st_size))
files=['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain','NLD_native/NFA_WALKER.c','NLD_native/NFA_MemoryLimit.c']
tools={n:dict(sha256=hashlib.sha256((B/n).read_bytes()).hexdigest(),bytes=(B/n).stat().st_size)for n in files}
(B/'NLD_TOOL_PINS.json').write_text(json.dumps(tools,indent=1)+'\n')
x=dict(export=str(dest),files=rows,bytes=sum(r['bytes']for r in rows),CARGO_TARGET_DIR=os.environ['CARGO_TARGET_DIR'],retained=True,deleted_files=0,workspace_bytes=sum(p.stat().st_size for p in B.rglob('*')if p.is_file()),disk=shutil.disk_usage(B)._asdict())
assert x['workspace_bytes']<30_000_000_000
(B/'NLD_EXPORT.json').write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps(dict(files=len(rows),bytes=x['bytes'],workspace_bytes=x['workspace_bytes'],free=x['disk']['free'])))
