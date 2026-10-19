import os,sys,subprocess,time,json,signal,hashlib
from pathlib import Path
base=Path(__file__).resolve().parent
source=Path(sys.argv[1]).resolve(); label=sys.argv[2]; module=sys.argv[3]
object_file=base/'lean-objects'/(module.replace('.','/')+'.olean'); object_file.parent.mkdir(parents=True,exist_ok=True)
source_root=source.parent.parent if module.startswith('AspisR1WithdrawalValidation.') else source.parent
env=dict(os.environ); env['LEAN_PATH']=str(base/'lean-objects')+(':'+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
cmd=['/usr/bin/time','-l',str(Path('/Users/dominic/.elan/bin/lake')),'env','python3','/Users/dominic/ZK/.worktrees/r1-j1-r11-r12-20261015/.j1-public-source-check/lean-with-cache.py',str(base/'lean-objects')+':/Users/dominic/ZK/external/aeneas/aeneas-verif-workspace/aeneas/backends/lean/.lake/build/lib/lean','-M6000','-R',str(source_root),'-o',str(object_file),str(source)]
checkout_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=source.parent,text=True).strip()
swap_before=subprocess.check_output(['/usr/sbin/sysctl','vm.swapusage'],text=True).strip()
start=time.monotonic(); peak=0; killed=False; killed_reason=None
with (base/(label+'.log')).open('w') as out:
 p=subprocess.Popen(cmd,cwd='/Users/dominic/ZK/external/aeneas/aeneas-verif-workspace/aeneas/backends/lean',env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  ps=subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True)
  usage=sum(int(z[2]) for line in ps.splitlines() if len(z:=line.split())==3 and int(z[1])==p.pid)
  peak=max(peak,usage)
  if usage>7*1024*1024 or time.monotonic()-start>180:
   killed=True; killed_reason='rss_guard' if usage>7*1024*1024 else 'timeout'; os.killpg(p.pid,signal.SIGKILL); break
  time.sleep(.1)
 rc=p.wait()
record={'module':module,'timeout_seconds':180,'killed_reason':killed_reason,'swap_before':swap_before,'swap_after':subprocess.check_output(['/usr/sbin/sysctl','vm.swapusage'],text=True).strip(),'command':cmd,'cwd':'/Users/dominic/ZK/external/aeneas/aeneas-verif-workspace/aeneas/backends/lean','source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'exit_status':rc,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_rss_kib_sampled':peak,'stop_threshold_kib':7*1024*1024,'killed_for_memory':killed,'source_base_revision':'953b7a55fdab799564b963060e4d9edc0d5545da','checkout_head':checkout_head,'source_status':'Exact checked bytes pinned by source_sha256; see bundle for new versus unchanged source classification','log':label+'.log','scope':'Focused local check using retained archived dependency objects; no package-wide/cold build or build-host Lean job; reads existing Aeneas backend cache only; compiler/cache compatibility is checked, not assumed; no dependency build.'}
(base/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2)); print((base/(label+'.log')).read_text())
sys.exit(rc)
