import os,sys,subprocess,time,json,signal,hashlib
from pathlib import Path
base=Path(__file__).resolve().parent
source=Path(sys.argv[1]).resolve(); label=sys.argv[2]
env=dict(os.environ); env['LEAN_PATH']=str(base/'objects')+(':'+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
cmd=['/usr/bin/time','-l',str(Path('/Users/dominic/.elan/bin/lake')),'env','python3',str(base/'lean-with-cache.py'),str(base/'objects')+':'+'/Users/dominic/.cache/aspis/r1-j1-r7-r8-local-check-20261015-7c5ca8699/objects:'+str(base.parent/'.j1-merge-check/objects'),'-M6000','-R',str(source.parent),'-o',str(base/'objects'/(source.stem+'.olean')),str(source)]
checkout_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=source.parent,text=True).strip()
start=time.monotonic(); peak=0; killed=False
with (base/(label+'.log')).open('w') as out:
 p=subprocess.Popen(cmd,cwd='/Users/dominic/ZK/AspisFormal',env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  ps=subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True)
  usage=sum(int(z[2]) for line in ps.splitlines() if len(z:=line.split())==3 and int(z[1])==p.pid)
  peak=max(peak,usage)
  if usage>7*1024*1024:
   killed=True; os.killpg(p.pid,signal.SIGKILL); break
  time.sleep(.1)
 rc=p.wait()
record={'command':cmd,'cwd':'/Users/dominic/ZK/AspisFormal','source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'exit_status':rc,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_rss_kib_sampled':peak,'stop_threshold_kib':7*1024*1024,'killed_for_memory':killed,'source_base_revision':'46ea40bbd6ec5ae5a63e99e08df7f3e5dd79fb04','checkout_head':checkout_head,'source_status':'Exact checked bytes pinned by source_sha256; see bundle for new versus unchanged source classification','log':label+'.log','scope':'Focused local check using retained archived dependency objects; no package-wide/cold build or build-host Lean job; uses previously audited merge dependency cache read-only; no dependency rebuild in this check.'}
(base/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2)); print((base/(label+'.log')).read_text())
sys.exit(rc)
