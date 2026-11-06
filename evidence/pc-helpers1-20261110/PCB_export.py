from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code=r'''
from pathlib import Path
import hashlib,json,lzma,shutil
B=Path('/home/dombarker/project-offloads/codex-pc-helpers1-20261110');C=Path('/home/dombarker/project-offloads/codex-pc-helpers1-cache-20261110');X=C/'PCB_exports_20261110';X.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
imports=json.loads(lzma.decompress((B/'PCB_IMPORTS.json.xz').read_bytes()));bad=[]
for rel,v in imports.items():
 p=C/rel
 if sha(p)!=v['sha256']:bad.append(rel)
assert not bad,bad
rows=[]
for kind in ['PCB_objects','PCB_generated']:
 for p in (B/kind).rglob('*'):
  if p.is_file():
   rel=p.relative_to(B/kind);out=X/kind/rel;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,out);assert sha(p)==sha(out)
   rows.append(dict(path=str(out),sha256=sha(out),bytes=out.stat().st_size,role='CANDIDATE if Final/Registry/AppendScalar/COMBINED_IMPORT; other accepted root packets remain as gated in L043-L045'))
for n in ['PCB_native/PCB_AuditDriver','PCB_native/PCB_WALKER.c','PCB_native/PCB_MemoryLimit.c','PCB_IMPORTS.json.xz']:
 p=B/n;out=X/n;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,out);rows.append(dict(path=str(out),sha256=sha(out),bytes=out.stat().st_size))
tools={}
for n in ['/home/dombarker/.cargo/bin/cargo-kani','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake',str(B/'S2W_run_host.py'),'/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py']:
 p=Path(n);tools[n]=dict(sha256=sha(p),bytes=p.stat().st_size)
audit=sha(B/'PCB_native/PCB_AuditDriver');assert audit=='ae859bcf5d757d584aff818e04099913fe1caa878f7bd64e88e8ca536f7a16aa'
result=dict(exports=str(X),copy_only=True,objects=rows,tools=tools,seed_import_count=len(imports),seed_full_hash_verification='PASS',audit_binary_unchanged=True,host_disk=shutil.disk_usage(B)._asdict(),caution='29-root combined object is a CANDIDATE; L060 failed at preparation raw/collector mismatch. Accepted23 combined source must be rebuilt by consumer; do not treat candidate aggregate as CLOSED.')
(X/'PCB_EXPORT_MANIFEST.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
v=json.loads(r.stdout);(E/'PCB_EXPORT_MANIFEST.json').write_text(json.dumps(v,indent=1)+'\n');print('PCB exports copied; all imported hashes revalidated; audit binary unchanged')
