"""Retain ONLY this job's objects, then remove this job's rebuildable scratch.
No compiler/prover runs. No shared workspace or retained cache is removed.
"""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
remote=r'''
from pathlib import Path
import hashlib,json,shutil,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-parser-20261104')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-parser-cache-20261104')
active=subprocess.check_output(['ps','-eo','pid,args'],text=True)
assert not any(str(B) in l and any(x in l for x in ['S2W_run_host.py','cargo-kani','/bin/lean ']) for l in active.splitlines()),'own build still active'
export=C/'NGD_exports_20261104';export.mkdir(exist_ok=True)
rows=[]
for p in sorted((B/'NGD_objects').rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(B/'NGD_objects');q=export/rel;q.parent.mkdir(parents=True,exist_ok=True)
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,('export collision',rel)
 else:shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 rows.append(dict(relative=str(rel),bytes=q.stat().st_size,sha256=h))
assert rows
# Hash observed tools without executing Rust/Kani/Lean outside a capped scope.
tools={}
for name,p in [('lean',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')),('cargo-kani',Path('/home/dombarker/.cargo/bin/cargo-kani'))]:
 q=p.resolve();tools[name]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest())
removed=[]
for n in ['NGD_target','NGD_ref_target','NGD_ref/target','NGD_tmp','NGD_objects']:
 p=B/n
 if p.exists():
  assert p.is_relative_to(B) and not p.is_symlink()
  size=sum(x.stat().st_size for x in p.rglob('*')if x.is_file())
  shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
print(json.dumps(dict(export=str(export),files=rows,total_bytes=sum(r['bytes']for r in rows),verified_before_scratch_removal=True,removed=removed,observed_tool_hashes=tools,tools_observed_after_campaign=True,disk=shutil.disk_usage(B)._asdict())))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=remote,capture_output=True,text=True)
 with(E/'NGD_CACHE_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 # Do not blindly repeat a possibly submitted mutation; recover export/removal
 # state read-only and make a new explicit recovery plan.
 raise RuntimeError('Transport after possible file-operation submission; recover read-only')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NGD_CACHE_EXPORTS.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(files=len(x['files']),export_bytes=x['total_bytes'],removed_bytes=sum(z['bytes']for z in x['removed']),free_bytes=x['disk']['free'])))
