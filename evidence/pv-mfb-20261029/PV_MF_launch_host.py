from pathlib import Path
import json,subprocess,sys,os,time
D=Path('/home/dombarker/project-offloads/codex-pv-mfb-20261029');G=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy')
n=int(sys.argv[2]);row=sys.argv[1];assert 69600<=n<=69699;O=D/('lean-'+str(n));O.mkdir(exist_ok=True)
cd=D/'cooldown.json'
if cd.exists() and time.time()<json.load(open(cd))['until']:sys.exit(78)
with (O/'admission.log').open('w') as o:a=subprocess.run(['python3',str(G/'reservation.py'),str(O/'admission.json')],stdout=o,stderr=subprocess.STDOUT)
if a.returncode or json.load(open(O/'admission.json')).get('allowed') is not True:
 cd.write_text(json.dumps(dict(until=time.time()+180)));sys.exit(78)
env=dict(os.environ,PV_REV=json.load(open(D/'dlib-preflight-input.json'))['current_revision'])
cmd=['systemd-run','--user','--scope','--unit=pv-mfb-lean-'+str(n),'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(O/'barrier.json'),'python3','/home/dombarker/project-offloads/codex-pv-b3p6-20261028/capped.py',str(O/'receipt'),'focused statement check; verified unchanged objects reused, no proof generation','--','python3',str(D/'PV_MF_check_dlib_host.py'),row,str(n)]
with (O/'scope.log').open('w') as o:a=subprocess.run(cmd,env=env,stdout=o,stderr=subprocess.STDOUT)
if not (O/'receipt/receipt.json').exists():
 if (O/'barrier.json').exists() and json.load(open(O/'barrier.json')).get('allowed') is not True:cd.write_text(json.dumps(dict(until=time.time()+180)));sys.exit(78)
sys.exit(a.returncode)
