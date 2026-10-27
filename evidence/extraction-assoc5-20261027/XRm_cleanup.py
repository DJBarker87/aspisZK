from pathlib import Path
import hashlib,json,os,shutil,time
B=Path('/home/dombarker/project-offloads/codex-cx-extraction-assoc5-20261027')
C=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
assert B.name=='codex-cx-extraction-assoc5-20261027'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(B.glob('XRm_L*/receipt.json'))]
errors=[];selected={}
for r in receipts:
 if r['exit_status']:continue
 for k,v in r['deps_fingerprint']['selected_objects'].items():
  p=Path(v['path'])
  if not p.exists() or sha(p)!=v['sha256']:errors.append({'attempt':r['attempt'],'dependency':str(p)})
  selected[str(p)]=v
objects=[]
for p in sorted((B/'XRm_objects').glob('*')):
 if p.is_file():objects.append({'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size})
runners={n:{'sha256':sha(B/n),'matches_coherent':sha(B/n)==sha(C/n)} for n in ['S2W_lean_host.py','S2W_run_host.py']}
live=[]
for d in Path('/proc').iterdir():
 if not d.name.isdigit() or int(d.name) in [os.getpid(),os.getppid()]:continue
 try:cmd=(d/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
 except (FileNotFoundError,PermissionError,ProcessLookupError):continue
 if str(B) in cmd and any(s in cmd for s in ['bin/lean ','cargo-kani','cbmc ','S2W_lean_host.py','S2W_run_host.py']):live.append({'pid':int(d.name),'command':cmd})
assert not live,live
# Solver files without a run-identifying path cannot safely be attributed to
# this job on the shared host. Retain other jobs' files.
tmp=[]
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in Path('/tmp').glob(pattern):
  try:s=p.stat();tmp.append({'path':str(p),'bytes':s.st_size,'mtime':s.st_mtime,'uid':s.st_uid})
  except FileNotFoundError:pass
removed=[]
for n in ['XRm_target','XRm_crate','XRm_objects','.lake']:
 p=B/n
 if p.exists():
  size=sum(f.stat().st_size for f in p.rglob('*') if f.is_file() and not f.is_symlink())
  shutil.rmtree(p);removed.append({'path':str(p),'bytes':size})
result={'utc':time.time(),'selected_dependencies':selected,'dependency_errors':errors,'objects_before_cleanup':objects,'runners':runners,'live_own':live,'removed':removed,'solver_temp_scan':tmp,'solver_cleanup':'No run-identifying solver temp path was emitted by K007/K010; no unambiguously attributable residual file; unrelated shared /tmp files retained.','shared_coherent_cache':'retained unchanged','keys':'no keys read, deleted or modified'}
(B/'XRm_cleanup.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'dependency_errors':len(errors),'objects':len(objects),'removed_bytes':sum(x['bytes'] for x in removed),'solver_candidates':len(tmp),'runners_identical':all(v['matches_coherent'] for v in runners.values())}))
