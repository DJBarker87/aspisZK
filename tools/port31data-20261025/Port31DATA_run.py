#!/usr/bin/env python3
"""Two charged local attempts only; no warmups, network or host jobs."""
import datetime, fcntl, hashlib, json, os, pathlib, re, signal, stat, subprocess, sys, time
from zoneinfo import ZoneInfo
T=pathlib.Path(__file__).resolve().parent
E=T.parents[1]/'evidence/port31data-20261025'
SYS=pathlib.Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0')
def pin(p):
 p=pathlib.Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def state(p):
 s=pathlib.Path(p).lstat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_mode,s.st_uid,s.st_nlink]
def safe(p):
 p=pathlib.Path(p)
 for q in [p,*p.parents]:assert not q.is_symlink(),str(q)
 s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_uid==501 and (s.st_nlink==1 or p.is_relative_to(SYS)),str(p)
 return p
if __name__=='__main__':
 n=int(sys.argv[1]);assert n in [353,354]
 rec=E/f'Port31DATA_attempt-{n}.json';assert not rec.exists()
 lock=pathlib.Path('/private/tmp/aspis-local-lean.lock.d')
 try:lock.mkdir(mode=0o700)
 except FileExistsError:print('WAITING: local Lean lock busy; no charge');sys.exit(2)
 gl=None
 try:
  (lock/'Port31DATA-owner.json').write_text(json.dumps(dict(pid=os.getpid(),branch='codex/cx-port31-body-data-20261025')))
  assert not subprocess.run(['pgrep','-x','lean'],capture_output=True,text=True).stdout.strip(),'WAITING: other Lean; no charge'
  now=datetime.datetime.now(ZoneInfo('Europe/London'))
  if 14<=now.hour<22 or now.hour==22 and now.minute<30:
   gl=open('/private/tmp/aspis-r0-lean.lock','a');fcntl.flock(gl,fcntl.LOCK_EX|fcntl.LOCK_NB)
  prep=json.loads((E/f'Port31DATA_preflight-{n}.json').read_text())
  for x in prep['fresh_pins']:assert pin(safe(x['path']))==x,x['path']
  for x in prep['states']:assert state(safe(x['path']))==x['stat'],x['path']
  paths=[x['path'] for x in prep['states']]
  lf=subprocess.run(['/usr/sbin/lsof','-F','pan','--',*paths],capture_output=True,text=True)
  (E/f'Port31DATA_lsof-{n}.log').write_text(lf.stdout+lf.stderr)
  assert lf.returncode in [0,1] and not any(l in ['aw','au'] for l in lf.stdout.splitlines()),'writer check'
  out=pathlib.Path(prep['directory']);out.mkdir(exist_ok=True,mode=0o700)
  src=T/('Port31DATA_Bool.lean' if n==353 else 'Port31DATA_Raw.lean')
  cmd=['/usr/bin/time','-l',str(SYS/'bin/lean'),'-j1','-M4400','-DElab.async=false','-R',str(T)]
  if n==353:cmd+=['-o',str(out/'Port31DATA_Bool.olean')]
  cmd += [str(src)]
  env=os.environ.copy();env.update(LEAN_PATH=str(SYS/'lib/lean'),PORT31_DATA=str(out))
  r=dict(command=cmd,env={k:env[k] for k in ['LEAN_PATH','PORT31_DATA']},source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source=pin(src),launcher=pin(__file__),preflight=pin(E/f'Port31DATA_preflight-{n}.json'),global_actual_after_charge=n,job_charged=n-352,global_ceiling=368,unassigned=2,reserved_kernel_consumers=5,carry=7,status='CHARGED BEFORE ACTUAL LAUNCH',print_axioms='PENDING' if n==353 else 'N/A: raw data only',aggregate_stop_bytes=8*1024**3,deadline_seconds=540)
  rec.write_text(json.dumps(r,indent=2)+'\n');start=time.monotonic();peak=0;stop=None
  with (E/f'Port31DATA_stdout-{n}.log').open('xb') as o,(E/f'Port31DATA_time-{n}.log').open('xb') as e:
   p=subprocess.Popen(cmd,cwd=T,env=env,stdout=o,stderr=e,start_new_session=True)
   while p.poll() is None:
    rows=[tuple(map(int,l.split())) for l in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines()];ids={p.pid}
    while True:
     nxt=ids|{pid for pid,parent,rss in rows if parent in ids}
     if nxt==ids:break
     ids=nxt
    rss=sum(rss*1024 for pid,parent,rss in rows if pid in ids);peak=max(peak,rss)
    if rss>=8*1024**3 or time.monotonic()-start>=540:
     stop='aggregate8GiB/deadline540s';os.killpg(p.pid,signal.SIGKILL);break
    time.sleep(.1)
   code=p.wait()
  logs=(E/f'Port31DATA_stdout-{n}.log').read_text();tim=(E/f'Port31DATA_time-{n}.log').read_text()
  r.update(exit_status=code,wall_seconds=time.monotonic()-start,aggregate_peak_rss_bytes=peak,stopped=stop,post_stat_unchanged=all(state(x['path'])==x['stat'] for x in prep['states']),post_fresh_hash_unchanged=all(pin(x['path'])==x for x in prep['fresh_pins']))
  for suffix,key in [('maximum resident set size','peak_process_rss_bytes'),('swaps','swaps')]:
   m=re.search(r'^\s*(\d+)\s+'+suffix+r'\s*$',tim,re.M);r[key]=int(m[1]) if m else None
  if n==353:r['print_axioms']=logs
  r['accepted']=code==0 and 'error:' not in logs and 'PANIC' not in logs and r['post_stat_unchanged'] and r['post_fresh_hash_unchanged']
  r['outputs']=[pin(x) for x in sorted(out.rglob('*')) if x.is_file()]
  r['status']='FINISHED; no unchanged retry';rec.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));sys.exit(0 if r['accepted'] else 1)
 finally:
  if gl:gl.close()
  (lock/'Port31DATA-owner.json').unlink();lock.rmdir()
