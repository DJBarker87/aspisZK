import os,sys,subprocess,time,json,signal,hashlib
from pathlib import Path
base=Path(__file__).resolve().parent
label=sys.argv[1]; cwd=Path(sys.argv[2]).resolve()
cmd=['/usr/bin/time','-l',*sys.argv[3:]]
env=dict(os.environ,CARGO_TARGET_DIR='/Users/dominic/ZK/target')
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=cwd,text=True).strip()
start=time.monotonic(); peak=0; killed=False
with (base/(label+'.log')).open('w') as out:
 p=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  ps=subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True)
  usage=sum(int(z[2]) for line in ps.splitlines() if len(z:=line.split())==3 and int(z[1])==p.pid)
  peak=max(peak,usage)
  if usage>3_145_728:
   killed=True; os.killpg(p.pid,signal.SIGKILL); break
  time.sleep(.05)
 rc=p.wait()
sources={}
for root in ['programs/r1-cost-probe','programs/aspis-pool','programs/aspis-registry','crates/aspis-statement','crates/aspis-r1-cost-probe','programs/aspis-verifier','crates/aspis-pool-wallet-v1','tools/r1-cost-probe','tools/v7-txv1-honest-proof']:
 for source in (cwd/root).rglob('*'):
  if source.is_file() and (source.suffix=='.rs' or source.name=='Cargo.toml'):
   sources[str(source.relative_to(cwd))]=hashlib.sha256(source.read_bytes()).hexdigest()
record={'command':cmd,'cwd':str(cwd),'checkout_head':revision,'sources_sha256':sources,'exit_status':rc,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_rss_kib_sampled':peak,'stop_threshold_kib':3_145_728,'killed_for_memory':killed,'log':label+'.log','scope':'Focused record parser differential/framing/canonicality tests; jobs2; 3GiB RSS stop below3.5GiB authorized ceiling; no proofgen/SBF/host'}
(base/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='sources_sha256'},indent=2))
print((base/(label+'.log')).read_text()[-9000:])
sys.exit(rc)
