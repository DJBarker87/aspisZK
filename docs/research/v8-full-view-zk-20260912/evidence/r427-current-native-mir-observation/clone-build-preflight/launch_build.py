#!/usr/bin/env python3
"""Stage and launch the focused R427 release build after lead approval."""
import hashlib, json, os, pathlib, shlex, subprocess

HERE=pathlib.Path(__file__).resolve().parent
PLAN=HERE/'launch-plan-v2.json'
HOST='dombarker@100.108.41.90'
SSH=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
REMOTE_STAGE='/tmp/aspis-r427-raw-mir-observer-20261002-a/build-attempt-v2'
REMOTE_SOURCE='/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon'
REMOTE_UNIT='aspisr427-build.service'

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def run(argv): return subprocess.run(argv,check=True)

def main():
 if os.environ.get('R427_ALLOW_BUILD')!='1': raise SystemExit('preparation only; require R427_ALLOW_BUILD=1 after lead review and successful clone audit')
 plan=json.loads(PLAN.read_text())
 p=HERE/'run_cached_build_remote.py'
 if sha(p)!=plan['run_cached_build_remote_sha256']: raise SystemExit('build worker does not match reviewed launch plan')
 clone_receipt=HERE.parent/'clone-launch-v2/clone-audit/clone-audit.json'
 if sha(clone_receipt)!=plan['clone_audit_sha256']: raise SystemExit('completed clone receipt does not match launch plan')
 remote_worker=f'{REMOTE_STAGE}/run_cached_build_remote.py'
 subprocess.run(['ssh',*SSH,HOST,'mkdir','-p',REMOTE_STAGE],check=True)
 run(['scp',*SSH,str(p),f'{HOST}:{remote_worker}'])
 remote_argv=['systemd-run','--user','--wait','--collect','--pipe',f'--unit={REMOTE_UNIT}',f'--working-directory={REMOTE_SOURCE}','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','/usr/bin/time','-v','-o',f'{REMOTE_STAGE}/build-gnu-time.txt','/usr/bin/env','R427_ALLOW_BUILD=1','python3',remote_worker]
 output=subprocess.run(['ssh',*SSH,HOST,shlex.join(remote_argv)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,check=False)
 (HERE/'build-launch-v2.stdout.log').write_text(output.stdout)
 (HERE/'build-launch-v2.status.json').write_text(json.dumps({'ssh_exit_status':output.returncode,'remote_unit':REMOTE_UNIT,'remote_argv':remote_argv,'launch_plan_sha256':sha(PLAN)},indent=2)+'\n')
 local=HERE/'build-attempt-v2';local.mkdir(exist_ok=False)
 remote_audit='/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a/candidate-audit/build-attempt-v2'
 collection=[]
 for name in ['build-command.json','build-host-reservation-before.json','build.log','cargo-gnu-time.txt','build-result.json','cgroup-samples.json','toolchain.txt','build-host-reservation-after.json']:
  result=subprocess.run(['scp',*SSH,f'{HOST}:{remote_audit}/{name}',str(local/name)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,check=False)
  collection.append({'name':name,'scp_exit_status':result.returncode,'output':result.stdout})
 result=subprocess.run(['scp',*SSH,f'{HOST}:{REMOTE_STAGE}/build-gnu-time.txt',str(local/'outer-gnu-time.txt')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,check=False)
 collection.append({'name':'outer-gnu-time.txt','scp_exit_status':result.returncode,'output':result.stdout})
 (HERE/'build-attempt-v2-collection-status.json').write_text(json.dumps(collection,indent=2)+'\n')
 return 0 if output.returncode==0 and all(x['scp_exit_status']==0 for x in collection) else 2

if __name__=='__main__': raise SystemExit(main())
