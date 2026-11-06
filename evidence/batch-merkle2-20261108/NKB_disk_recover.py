from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import shutil,json,hashlib,time
b=Path('/home/dombarker/project-offloads/codex-cx-batch-merkle2-20261108');t=b/'NKB_target'
objects=[dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted((b/'NKB_objects').rglob('*')) if p.is_file()]
before=shutil.disk_usage(b);files=[p for p in t.rglob('*') if p.is_file()];total=sum(p.stat().st_size for p in files)
# Only this job's disposable Cargo build-output directory. No retained cache/source/receipt is removed.
assert t.resolve()==b/'NKB_target'
shutil.rmtree(t)
d=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKB_20261108/NKB_exports_20261108');d.mkdir(exist_ok=True)
for x in objects:
 p=Path(x['path']);q=d/p.relative_to(b/'NKB_objects');q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q);assert hashlib.sha256(q.read_bytes()).hexdigest()==x['sha256']
print(json.dumps(dict(timestamp=time.time(),free_before=before.free,free_after=shutil.disk_usage(b).free,removed_target_bytes=total,retained_export=str(d),objects=objects),indent=2))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NKB_DISK_RECOVERY.json').write_text(r.stdout);x=json.loads(r.stdout);print('Owned Cargo outputs removed; export verified; free bytes:',x['free_after'])
