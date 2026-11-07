from pathlib import Path
import json,re,hashlib,shutil,os
B=Path('/home/dombarker/project-offloads/codex-cx-cut-pilot-20261110');active=[]
for p in Path('/proc').glob('[0-9]*'):
 try:cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
 except (PermissionError,ProcessLookupError,FileNotFoundError):continue
 if p.name!=str(os.getpid()) and (re.search(r'\bNMD_[KL]\d{3}\.json\b',cmd) or str(B/'NMD_native/') in cmd):active.append(dict(pid=p.name,command=cmd))
assert not active,active
removed=[]
for pattern in ['external-sat*.cnf','external-sat*.out','smt2_dec_problem*']:
 for p in (B/'NMD_tmp').glob(pattern):
  if not p.is_file() or p.is_symlink():continue
  h=hashlib.sha256()
  with p.open('rb') as f:
   while chunk:=f.read(1024*1024):h.update(chunk)
  removed.append(dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest(),kind='own solver temporary'));p.unlink()
x=dict(active_owned_jobs=active,removed_solver_temporaries=removed,cache_target_tmp_directories_retained=True,keys_touched=0,workspace_bytes=sum(p.stat().st_size for p in B.rglob('*') if p.is_file()),free_bytes=shutil.disk_usage(B).free)
(B/'NMD_HOST_TERMINAL.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
