"""Remove only this job's rebuildable caches; never traverse shared sources."""
from pathlib import Path
import subprocess,json,shlex
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-leaf-p6-11-20261027'
script='''from pathlib import Path
import os,json,shutil,datetime
b=Path(BASE);live=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  argv=(p/'cmdline').read_bytes().split(b'\\0'); name=Path(os.fsdecode(argv[0])).name
  if name in ['lean','cargo-kani','kani-driver','cbmc','rustc','kani-compiler'] and (str(b) in os.fsdecode((p/'cmdline').read_bytes()) or (p/'cwd').resolve()==b):live.append(p.name)
 except (OSError,IndexError):pass
assert not live,live
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'live_owned_provers':live,'removed':[],'retained_sources':str(b/'LPm_src'),'key_operations':False}
for n in ['LPm_tmp','LPm_target','LPm_objects']:
 p=b/n
 assert not p.is_symlink(),str(p)
 if p.exists():
  files=[q for q in p.rglob('*') if q.is_file()]
  item={'path':str(p),'files':len(files),'bytes':sum(q.stat().st_size for q in files)}
  if n=='LPm_tmp':item['solver_files']=[str(q) for q in files if 'external-sat' in q.name or 'smt2_dec_problem' in q.name]
  shutil.rmtree(p);item['absent_after']=not p.exists();out['removed'].append(item)
print(json.dumps(out,indent=2))
'''.replace('BASE',repr(B))
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],capture_output=True,text=True)
(E/'LPm_CLEANUP.stderr').write_text(r.stderr)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);out['ssh_exit_status']=r.returncode
(E/'LPm_CLEANUP.json').write_text(json.dumps(out,indent=2)+'\n')
print(r.stdout)
