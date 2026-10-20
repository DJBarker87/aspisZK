from pathlib import Path
import subprocess,time,os,json,hashlib,signal,re
w=Path(__file__).resolve().parent;e=w/'native';e.mkdir(exist_ok=False)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
rustc=Path(subprocess.check_output(['rustup','which','rustc'],cwd=w,text=True).strip());src=w/'src/lib.rs'
(e/'preflight.json').write_text(json.dumps({'source_sha256':sha(src),'source_binding_sha256':sha(w/'source-binding.json'),'rustc':str(rustc),'rustc_sha256':sha(rustc),'version':subprocess.check_output([str(rustc),'-vV'],text=True),'limits':{'aggregate_rss_bytes':2*2**30,'wall_seconds':60},'expected_time':'Tiny optimized compile and fixed regression controls; no symbolic proof in this native phase.'},indent=2)+'\n')
def rss(pid):
 rows={int(a):(int(b),int(c)*1024) for a,b,c in (s.split() for s in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines())};active={pid}
 while True:
  add={p for p,(parent,r) in rows.items() if parent in active}-active
  if not add:break
  active|=add
 return sum(rows.get(p,(0,0))[1] for p in active)
for phase,argv in [('compile',[str(rustc),'--edition=2021','-O','--test',str(src),'-o',str(w/'native-test')]),('controls',[str(w/'native-test'),'--nocapture'])]:
 start=time.monotonic();peak=0;reason=None
 with (e/(phase+'.log')).open('w') as f:
  cmd=['/usr/bin/time','-l','-o',str(e/(phase+'.time.log'))]+argv
  p=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,start_new_session=True,cwd=w)
  while p.poll() is None:
   peak=max(peak,rss(p.pid))
   if peak>=2*2**30 or time.monotonic()-start>60:
    reason='resource cap';os.killpg(p.pid,signal.SIGTERM);break
   time.sleep(.1)
  code=p.wait()
 txt=(e/(phase+'.time.log')).read_text();get=lambda pat:int(re.search(pat,txt)[1]) if re.search(pat,txt) else None
 rec={'command':cmd,'exit_status':code,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_rss_bytes':peak,'peak_process_rss_bytes':get(r'(\d+)\s+maximum resident set size'),'swaps':get(r'(\d+)\s+swaps'),'watchdog_abort':reason,'source_sha256':sha(src),'print_axioms':'N/A: native Rust regression controls, not Lean or universal proof'}
 (e/(phase+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec))
 if code or reason:raise SystemExit(code or 1)
