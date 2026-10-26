"""Job orchestration using unchanged existing host admission and Lean launchers."""
from pathlib import Path
import subprocess,json,sys,time
E=Path(__file__).resolve().parent; H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
for i in range(int(sys.argv[1]),int(sys.argv[2])+1):
 a=f'TAu_{i:03d}';mod=f'TAu_Audit{i:03d}'
 cfg=json.loads((E/(a+'.json')).read_text())
 assert cfg['command'][-2]=='-DElab.async=false',cfg['command']
 subprocess.run(['scp','-q',str(E/(a+'.json')),str(E/(mod+'.lean')),H+':'+B+'/'],check=True)
 for retry in range(11):
  cmd=f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json'
  r=subprocess.run(['ssh',H,cmd],capture_output=True,text=True)
  (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
  if r.returncode==0:break
  if r.returncode==78 and retry<10:time.sleep(180);continue
  if 'FileNotFoundError' in r.stderr and retry==0:time.sleep(30);continue
  raise SystemExit('STOP reservation: '+r.stderr)
 else:raise SystemExit('STOP reservation retries exhausted')
 subprocess.run(['scp','-q',H+':'+B+'/'+a+'-reservation.json',str(E)],check=True)
 cmd=f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py {a}.json'
 r=subprocess.run(['ssh',H,cmd],capture_output=True,text=True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 collect=subprocess.run(['scp','-qr',H+':'+B+'/'+a,str(E)])
 if collect.returncode:raise SystemExit('STOP receipt collection failure')
 receipt=json.loads((E/a/'receipt.json').read_text())
 print(a,'exit',receipt['exit_status'],'wall',round(receipt['wall_seconds'],3),'rss',receipt['peak_rss_kib'],flush=True)
 if receipt['exit_status'] in [124,137]:raise SystemExit('STOP isolate timed/memory-killed queries before further runs')
