"""Read-only Stream A scope inventory; does not alter scopes."""
import subprocess,json,pathlib,time,shutil,sys
scopes=[]
for line in subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True).splitlines():
 unit=line.split()[0]
 if unit=='init.scope':continue
 cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip()
 dirs=set()
 try:
  for f in (pathlib.Path('/sys/fs/cgroup')/cg.lstrip('/')).rglob('cgroup.procs'):
   for pid in f.read_text().split():
    try:dirs.add(str((pathlib.Path('/proc')/pid/'cwd').resolve(strict=True)))
    except (OSError,RuntimeError):pass
 except OSError:continue
 if any(d.startswith('/home/dombarker/project-offloads/codex-cx-') for d in dirs):scopes.append(dict(scope=unit,working_directories=sorted(dirs)))
print(json.dumps(dict(time=time.time(),stream_a_count=len(scopes),scopes=scopes,free_bytes=shutil.disk_usage('/home/dombarker/project-offloads').free)))
