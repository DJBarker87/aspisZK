"""JFm task orchestration; invokes unchanged host admission and Lean launcher."""
from pathlib import Path
import json,subprocess,sys,time,shlex
P=Path(__file__).resolve().parent; R=P.parents[1]
B='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'; HOST='dombarker@100.108.41.90'
def ssh(cmd,**kw):return subprocess.run(['ssh',HOST,cmd],**kw)
n=int(sys.argv[1]); mod=sys.argv[2]; assert 1<=n<=100
source_file=R/'lean'/(mod+'.lean')
if not mod.startswith('JFm_'):
 assert mod in json.loads((P/'JFm_MISSING_CLOSURE.json').read_text()),mod
 source_file=R/'docs/research/100bit-spend-path-20261013/lean'/(mod+'.lean')
 # Existing tracked modules are rebuilt byte-identically; no source edits.
 assert subprocess.check_output(['git','show','HEAD:'+str(source_file.relative_to(R))])==source_file.read_bytes()
a=f'JFm_{n:03}'; assert not (P/a).exists()
cfg=json.loads((R/'evidence/recount10-20261026/Rc10_001/receipt.json').read_text())
cfg.update(attempt=a,sources=[mod+'.lean'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=bool(subprocess.check_output(['git','status','--porcelain'])),expected_time='Focused JFm composition or atomic kernel inventory; no arithmetic aggregation')
cfg['env']['LEAN_PATH'] += ':/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/JFp_Cache:/home/dombarker/project-offloads/d18-circle-model-repin-v5-20261019/attempt/objects:/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023/objects'
cfg['command'][-3:]=['-o',mod+'.olean',mod+'.lean']
(P/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
retries=[]
for retry in range(11):
 cmd=f'python3 /home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier.log 2>&1'
 r=ssh(cmd)
 # Admission diagnostics are already durable on the host, before any scp.
 sshout=ssh(f'cat {B}/{a}-barrier.log',capture_output=True,text=True)
 (P/(a+'-barrier.log')).write_text(sshout.stdout+sshout.stderr)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if r.returncode==0 and exists:break
 if r.returncode==78 and retry<10:
  retries.append(dict(wait_seconds=180,reason='reservation contention')); print('Reservation contention; waiting 180s',flush=True);time.sleep(180);continue
 if (not exists or 'FileNotFoundError' in sshout.stdout) and retry==0:
  retries.append(dict(wait_seconds=30,reason='transient missing receipt/vanished cgroup'));time.sleep(30);continue
 print(sshout.stdout+sshout.stderr);sys.exit(r.returncode or 1)
subprocess.run(['scp','-q',str(source_file),str(P/(a+'.json')),HOST+':'+B+'/'],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py {a}.json',capture_output=True,text=True)
(P/(a+'-launch.log')).write_text(r.stdout+r.stderr); print(r.stdout+r.stderr)
subprocess.run(['scp','-qr',HOST+':'+B+'/'+a,str(P)],check=True)
subprocess.run(['scp','-q',HOST+':'+B+'/'+a+'-reservation.json',str(P)],check=True)
(P/(a+'-retries.json')).write_text(json.dumps(retries,indent=2)+'\n')
sys.exit(r.returncode)
