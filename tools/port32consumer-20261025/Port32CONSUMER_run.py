"""Only authorized actual local calls356/357. No probes or other compilers."""
import datetime,fcntl,json,os,pathlib,re,signal,subprocess,sys,time
from zoneinfo import ZoneInfo
from Port32CONSUMER_check import T,E,pin,state,safe
assert len(sys.argv)==2 and sys.argv[1] in ['356','357'];n=int(sys.argv[1]);rec=E/f'Port32CONSUMER_attempt-{n}.json';assert not rec.exists()
if n==357:
 old=json.loads((E/'Port32CONSUMER_attempt-356.json').read_text());assert not old['accepted']
 assert old['source']['sha256']!=pin(T/'Port32CONSUMER_Consumer.lean')['sha256'],'material source change required'
lock=pathlib.Path('/private/tmp/aspis-local-lean.lock.d')
try:lock.mkdir(mode=0o700)
except FileExistsError:print('WAIT: local lock busy, no charge');sys.exit(2)
gl=None
try:
 (lock/'Port32CONSUMER-owner.json').write_text(json.dumps(dict(pid=os.getpid(),branch='codex/cx-port32-consumer-20261025')))
 assert not subprocess.run(['pgrep','-ifl','(^|/)(lean|lake)( |$)'],capture_output=True,text=True).stdout.strip(),'other local Lean; no charge'
 now=datetime.datetime.now(ZoneInfo('Europe/London'))
 if 14<=now.hour<22 or now.hour==22 and now.minute<30:
  gl=open('/private/tmp/aspis-r0-lean.lock','a');fcntl.flock(gl,fcntl.LOCK_EX|fcntl.LOCK_NB)
 check=json.loads((E/'Port32CONSUMER_check.json').read_text());pre=json.loads((E/'Port32CONSUMER_preflight.json').read_text())
 for x in check['files']+check['api']+pre['pins']+pre['runtime']:assert pin(safe(x['path']))==x,x['path']
 for x in pre['states']:assert state(safe(x['path']))==x['stat'],x['path']
 paths=sorted({x['path'] for x in check['files']+check['api']+pre['pins']+pre['runtime']+pre['states']})
 lf=subprocess.run(['/usr/sbin/lsof','-F','pan','--',*paths],capture_output=True,text=True)
 (E/f'Port32CONSUMER_lsof-{n}.log').write_text(lf.stdout+lf.stderr)
 assert lf.returncode in [0,1] and not any(l in ['aw','au'] for l in lf.stdout.splitlines()),'writer check'
 assert not subprocess.check_output(['git','status','--porcelain','--','tools/port32consumer-20261025'],text=True).strip(),'source must be committed'
 SYS=pathlib.Path(pre['sysroot']);src=T/'Port32CONSUMER_Consumer.lean'
 cmd=['/usr/bin/time','-l',str(SYS/'bin/lean'),'-j1','-M4400','-DElab.async=false','-R',str(T),str(src)]
 env=os.environ.copy();env['LEAN_PATH']=str(SYS/'lib/lean')
 r=dict(command=cmd,environment=dict(LEAN_PATH=env['LEAN_PATH']),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source=pin(src),launcher=pin(__file__),preflight=pin(E/'Port32CONSUMER_preflight.json'),check=pin(E/'Port32CONSUMER_check.json'),status='CHARGED BEFORE ACTUAL LAUNCH',actual_after_charge=n,job_charged=n-355,job_max_calls=2,global_ceiling=368,remaining=368-n,other_reservations=dict(unassigned=1,other_reserved_consumer=3,carry=7),private_budgets_unchanged=True,host_other_budgets_used=0,deadline_seconds=540,aggregate_stop_bytes=8*1024**3,default_heartbeats_recDepth=True,print_axioms='PENDING',core_assessment=pre['core_assessment'])
 # The complete source is retained even if the second material change supersedes it.
 (E/f'Port32CONSUMER_source-{n}.lean.txt').write_bytes(src.read_bytes());rec.write_text(json.dumps(r,indent=2)+'\n')
 start=time.monotonic();peak=0;stop=None
 with (E/f'Port32CONSUMER_stdout-{n}.log').open('xb') as o,(E/f'Port32CONSUMER_time-{n}.log').open('xb') as e:
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
 log=(E/f'Port32CONSUMER_stdout-{n}.log').read_text();tim=(E/f'Port32CONSUMER_time-{n}.log').read_text()
 r.update(exit_status=code,wall_seconds=time.monotonic()-start,aggregate_peak_rss_bytes=peak,stopped=stop,post_stat_unchanged=all(state(x['path'])==x['stat'] for x in pre['states']),post_hash_unchanged=all(pin(x['path'])==x for x in check['files']+check['api']+pre['pins']+pre['runtime']),print_axioms=log,stdout=pin(E/f'Port32CONSUMER_stdout-{n}.log'),time_log=pin(E/f'Port32CONSUMER_time-{n}.log'))
 for suffix,key in [('maximum resident set size','peak_process_rss_bytes'),('swaps','swaps')]:
  m=re.search(r'^\s*(\d+)\s+'+suffix+r'\s*$',tim,re.M);r[key]=int(m[1]) if m else None
 r['accepted']=code==0 and 'error:' not in log and 'PANIC' not in log and 'PORT32_COMPLETE' in log and r['post_stat_unchanged'] and r['post_hash_unchanged']
 r['status']='FINISHED; no unchanged retry'
 r['output_pins']=[pin(x) for x in pathlib.Path('/private/tmp/Port32CONSUMER-20261025').iterdir() if x.is_file()]
 rec.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['exit_status','wall_seconds','aggregate_peak_rss_bytes','peak_process_rss_bytes','swaps','accepted','actual_after_charge','remaining']}));sys.exit(0 if r['accepted'] else 1)
finally:
 if gl:gl.close()
 (lock/'Port32CONSUMER-owner.json').unlink();lock.rmdir()
