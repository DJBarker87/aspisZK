import hashlib,json,os,pathlib,shlex,subprocess,time
R=pathlib.Path(__file__).resolve().parents[1]
if os.environ.get('R427_ALLOW_DIRECT_DRIVER_BUILD')!='1':raise SystemExit('Root-reviewed direct build gate closed')
OUT=R/'lead-direct-launch';OUT.mkdir(exist_ok=False)
HOST='dombarker@100.108.41.90'
SSH=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null',HOST]
STAGE='/tmp/aspis-r427-raw-mir-observer-20261002-a/direct-driver-build'
ROOT='/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a'
FILES=[R/'direct-driver-build/run_direct_driver_remote.py',R/'lead-audit/direct-driver-input-selection.json',R/'clone-launch-v2/clone-audit/target-cache-sha256.json']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
compile(FILES[0].read_text(),str(FILES[0]),'exec')
record={'classification':'root-reviewed direct driver compiler launch; no Cargo/no dependency build','files':{p.name:sha(p) for p in FILES},'expected_time':'one driver compilation, code generation and linking','caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}}
(OUT/'launch-inputs.json').write_text(json.dumps(record,indent=2)+'\n')
for p in FILES:(OUT/p.name).write_bytes(p.read_bytes())
def run(args,name,blob=None):
 started=time.monotonic()
 with (OUT/(name+'.stdout')).open('wb') as out,(OUT/(name+'.stderr')).open('wb') as err:
  v=subprocess.run(args,input=blob,stdout=out,stderr=err)
 (OUT/(name+'.status.json')).write_text(json.dumps({'exit_status':v.returncode,'wall_seconds':time.monotonic()-started,'argv':args},indent=2)+'\n')
 return v.returncode
remote=shlex.join(['python3','-c',"import pathlib; pathlib.Path("+repr(STAGE)+").mkdir(exist_ok=False)"])
rc=run(SSH+[remote],'stage-create')
if rc:raise SystemExit(rc)
for p in FILES:
 remote=shlex.join(['python3','-c',"import pathlib,sys; pathlib.Path("+repr(STAGE+'/'+p.name)+").write_bytes(sys.stdin.buffer.read())"])
 rc=run(SSH+[remote],'stage-'+p.name,p.read_bytes())
 if rc:raise SystemExit(rc)
argv=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspisr427-direct-driver','--working-directory='+ROOT+'/charon','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','KillMode=control-group','-p','TimeoutStopSec=10s','/usr/bin/time','-v','-o',STAGE+'/outer-gnu-time.txt','env','R427_ALLOW_DIRECT_DRIVER_BUILD=1','python3',STAGE+'/run_direct_driver_remote.py']
rc=run(SSH+[shlex.join(argv)],'direct-build')
remote=shlex.join(['python3','-c',"import pathlib,tarfile,sys; p=pathlib.Path("+repr(ROOT+'/candidate-audit/direct-driver-build')+"); t=tarfile.open(fileobj=sys.stdout.buffer,mode='w|'); t.add(p,arcname='direct-audit') if p.exists() else None; q=pathlib.Path("+repr(STAGE+'/outer-gnu-time.txt')+"); t.add(q,arcname='outer-gnu-time.txt') if q.exists() else None; t.close()"])
with (OUT/'direct-audit.tar').open('wb') as out,(OUT/'collect.stderr').open('wb') as err:
 v=subprocess.run(SSH+[remote],stdout=out,stderr=err)
(OUT/'collect.status.json').write_text(json.dumps({'exit_status':v.returncode})+'\n')
print(json.dumps({'direct_build_exit_status':rc,'collection_exit_status':v.returncode,'saved':str(OUT)},indent=2))
raise SystemExit(rc or v.returncode)
