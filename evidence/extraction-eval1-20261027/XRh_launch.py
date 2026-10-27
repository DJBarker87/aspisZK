"""Serial orchestration using unchanged host admission and command runner."""
from pathlib import Path
import subprocess,json,sys,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-extraction-eval1-20261027'
def ssh(s):return subprocess.run(['ssh',H,s],text=True,capture_output=True)
def collect(n):
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp','-q',H+':'+B+'/'+n,str(p)],check=True)
cfg=json.loads((E/sys.argv[1]).read_text());a=cfg['attempt']
for retry in range(11):
 n=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{n} 2>&1');collect(n)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if not exists and retry==0:time.sleep(30);continue
 if exists:
  collect(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
  if r.returncode==0 and ad['allowed']:break
  if (r.returncode==78 or 'quiet window' in ad.get('reason','')) and retry<10:
   print(a,'reservation wait 180s',flush=True);time.sleep(180);continue
 log=(E/n).read_text()
 if 'FileNotFoundError' in log and retry==0:time.sleep(30);continue
 raise SystemExit('STOP admission: '+log)
else:raise SystemExit('STOP admission retry budget')
cfg['reservation_retries']=retry;(E/sys.argv[1]).write_text(json.dumps(cfg,indent=2)+'\n')
for f in [sys.argv[1],*cfg['sources']]:subprocess.run(['scp','-q',str(E/f),H+':'+B+'/'+f],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 XRh_run_host.py {sys.argv[1]}')
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
print((E/a/'receipt.json').read_text(),flush=True)
