"""Remove only this job's rebuildable scratch after a verified retained export."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,hashlib,shutil,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-values-20261104')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-q-values-cache-20261104')
manifest=json.loads((C/'NFP_exports_20261104/NFP_EXPORT.json').read_text())
for r in manifest['files']:assert hashlib.sha256(Path(r['destination']).read_bytes()).hexdigest()==r['sha256']
# No launch is allowed after final budget use. Verify no process has a cwd
# inside this job, including a stopped compiler/solver, before removing files.
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  cwd=(p/'cwd').resolve(); cmd=(p/'cmdline').read_bytes().replace(b'\\0',b' ').decode(errors='replace')
  if cwd==B or B in cwd.parents:active.append(dict(pid=p.name,cwd=str(cwd),command=cmd))
 except (OSError,RuntimeError):pass
assert not active,active
names=['NFP_target','NFP_tmp','NFP_native','NFP_objects'];removed=[]
for n in names:
 p=B/n
 if not p.exists():continue
 files=[z for z in p.rglob('*') if z.is_file()]
 keys=[str(z) for z in files if z.name in ['id.json','keypair.json','wallet.json'] or z.name.endswith('-keypair.json')]
 assert not keys,dict(retain_key_candidates=keys)
 size=sum(z.stat().st_size for z in files);count=len(files)
 shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size,files=count))
result=dict(verified_export_files=len(manifest['files']),active_job_processes=active,removed=removed,own_cache_retained=C.exists(),cache=str(C),source_scratch_retained=str(B/'NFP_src'),no_wallet_or_key_cleanup=True,solver_temp_policy='Only own TMPDIR removed; no attribution-safe evidence that any shared /tmp solver file belongs to this job, so shared /tmp left untouched.',disk_usage=subprocess.check_output(['df','-h',str(B)],text=True))
(B/'NFP_CLEANUP.json').write_text(json.dumps(result,indent=2)+'\\n');print(json.dumps(result))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NFP_CLEANUP.log').write_text(r.stderr);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NFP_CLEANUP.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
