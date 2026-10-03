import hashlib,json,pathlib,shlex,subprocess,time
R=pathlib.Path(__file__).resolve().parents[1]
OUT=R/'clone-launch-v2'; OUT.mkdir(exist_ok=False)
HOST='dombarker@100.108.41.90'
SSH=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null',HOST]
STAGE='/tmp/aspis-r427-raw-mir-observer-20261002-a'
ROOT='/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a'
worker=R/'clone-build-preflight/prepare_clone_remote.py'; draft=R/'lead-draft/get_mir.diagnostic.UNVERIFIED.rs'
record={'phase':'isolated clone only; NO build/extraction','worker_sha256':hashlib.sha256(worker.read_bytes()).hexdigest(),'draft_sha256':hashlib.sha256(draft.read_bytes()).hexdigest(),'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}}
(OUT/'launch.json').write_text(json.dumps(record,indent=2)+'\n')
def run(args,name):
 started=time.monotonic()
 with (OUT/(name+'.stdout')).open('wb') as out,(OUT/(name+'.stderr')).open('wb') as err:
  p=subprocess.run(args,stdout=out,stderr=err)
 (OUT/(name+'.status.json')).write_text(json.dumps({'exit_status':p.returncode,'wall_seconds':time.monotonic()-started,'argv':args},indent=2)+'\n')
 return p.returncode
remote=shlex.join(['python3','-c',"import pathlib; p=pathlib.Path("+repr(STAGE)+"); assert p.is_dir(); assert (p/'prepare_clone_remote.py').is_file(); assert not pathlib.Path('/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a').exists()"])
status=run(SSH+[remote],'stage-create')
if status:raise SystemExit(status)
for src in (worker,draft):
 remote=shlex.join(['python3','-c',"import pathlib,sys; pathlib.Path("+repr(STAGE+'/'+src.name)+").write_bytes(sys.stdin.buffer.read())"])
 with (OUT/('stage-'+src.name+'.stdout')).open('wb') as out,(OUT/('stage-'+src.name+'.stderr')).open('wb') as err:
  p=subprocess.run(SSH+[remote],input=src.read_bytes(),stdout=out,stderr=err)
 (OUT/('stage-'+src.name+'.status.json')).write_text(json.dumps({'exit_status':p.returncode})+'\n')
 if p.returncode:raise SystemExit(p.returncode)
argv=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspisr427-clone','--working-directory=/home/dombarker/project-offloads','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','env','R427_ALLOW_CLONE=1','python3',STAGE+'/'+worker.name]
status=run(SSH+[shlex.join(argv)],'clone')
remote=shlex.join(['python3','-c',"import pathlib,tarfile,sys; p=pathlib.Path("+repr(ROOT+'/candidate-audit/clone')+"); print('clone_audit_exists='+str(p.exists()),file=sys.stderr); t=tarfile.open(fileobj=sys.stdout.buffer,mode='w|'); t.add(p,arcname='clone-audit') if p.exists() else None; t.close()"])
with (OUT/'clone-audit.tar').open('wb') as out,(OUT/'collect.stderr').open('wb') as err:
 p=subprocess.run(SSH+[remote],stdout=out,stderr=err)
(OUT/'collect.status.json').write_text(json.dumps({'exit_status':p.returncode})+'\n')
print(json.dumps({'clone_exit_status':status,'collection_exit_status':p.returncode,'evidence':str(OUT)},indent=2))
raise SystemExit(status or p.returncode)
