"""Task orchestration only: use unchanged host launchers and reservation gate."""
from pathlib import Path
import json,subprocess,sys,shlex,time
P=Path(__file__).resolve().parent; R=P.parents[1]
B='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
HOST='dombarker@100.108.41.90'
def ssh(cmd,**kw):return subprocess.run(['ssh',HOST,cmd],**kw)
n=int(sys.argv[1]);mod=sys.argv[2]; assert 1<=n<=100
attempt=f'FIu_{n:03}'
assert not (P/attempt).exists(),attempt
src=R/'lean'/f'{mod}.lean'; assert mod.startswith('FIu_')
cfg=json.loads((R/'evidence/recount5-20261026/Rc5_001.json').read_text())
paths=cfg['env']['LEAN_PATH'].split(':');paths.insert(1,'/home/dombarker/project-offloads/codex-cx-parse-final-20261026');paths.insert(1,B+'/F3Y_delivered')
cfg.update(attempt=attempt,sources=[src.name],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=bool(subprocess.check_output(['git','status','--porcelain'])),expected_time='Focused finish installation proof or statement audit; no arithmetic aggregation')
cfg['env']['LEAN_PATH']=':'.join(paths);cfg['command'][-3:]=['-o',mod+'.olean',src.name]
(P/(attempt+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
barrier=f'python3 /home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py {B}/{attempt}-reservation.json'
retries=[]
for retry in range(11):
 r=ssh(barrier+' > '+B+'/'+attempt+'-barrier.log 2>&1; reservation_status=$?; cat '+B+'/'+attempt+'-barrier.log; exit $reservation_status',capture_output=True,text=True)
 (P/(attempt+'-barrier.log')).write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode==78 and retry<10:
  retries.append(dict(retry=retry,wait_seconds=180,reason='reservation refused'))
  print('Reservation busy; waiting 180 seconds',flush=True);time.sleep(180);continue
 if 'FileNotFoundError' in (r.stdout+r.stderr) and retry==0:
  retries.append(dict(retry=retry,wait_seconds=30,reason=r.stdout+r.stderr));time.sleep(30);continue
 print(r.stderr);sys.exit(r.returncode)
subprocess.run(['scp','-q',str(src),str(P/(attempt+'.json')),HOST+':'+B+'/'],check=True)
cmd=f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py {attempt}.json'
r=ssh(cmd,capture_output=True,text=True);print(r.stdout+r.stderr)
subprocess.run(['scp','-qr',HOST+':'+B+'/'+attempt,str(P) ],check=True)
subprocess.run(['scp','-q',HOST+':'+B+'/'+attempt+'-reservation.json',str(P)],check=True)
(P/(attempt+'-retries.json')).write_text(json.dumps(retries,indent=2)+'\n')
sys.exit(r.returncode)
