"""Own isolated Kani launch,always behind the shared reservation barrier."""
from pathlib import Path
import json,subprocess,sys,time
P=Path(__file__).resolve().parent;R=P.parents[1]
B='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
W='/home/dombarker/project-offloads/codex-cx-finish-install15-20261027'
HOST='dombarker@100.108.41.90'
n=int(sys.argv[1]);harness=sys.argv[2];assert 17<=n<=20
attempt=f'FJe_K{n:03}';assert not (P/attempt).exists()
def ssh(cmd,**kw):return subprocess.run(['ssh',HOST,cmd],**kw)
subprocess.run([sys.executable,str(P/'FJe_prepare.py'),'/private/tmp/FJe_packed_inputs'],check=True)
cfg=json.loads((P/'FJe_K016.json').read_text());cfg.update(attempt=attempt,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=json.loads((P/'FJe_inputs.json').read_text()),expected_time=sys.argv[3]);cfg['command'][cfg['command'].index('--harness')+1]=harness
(P/(attempt+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
for retry in range(11):
 r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py {B}/{attempt}-reservation.json > {B}/{attempt}-barrier.log 2>&1; reservation_status=$?; cat {B}/{attempt}-barrier.log; exit $reservation_status',capture_output=True,text=True)
 (P/(attempt+'-barrier.log')).write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode==78 and retry<10:
  print('Reservation busy; waiting before retry',flush=True)
  for _ in range(6):time.sleep(30)
  continue
 sys.exit(r.returncode)
subprocess.run(['scp','-q','/private/tmp/FJe_packed_inputs/src/FJe_native.rs',HOST+':'+W+'/packed/src/'],check=True)
subprocess.run(['scp','-q',str(P/'FJe_reference.rs'),str(P/'FJe_inputs.json'),str(P/(attempt+'.json')),HOST+':'+B+'/'],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {attempt}.json');
subprocess.run(['scp','-qr',HOST+':'+B+'/'+attempt,str(P)],check=True)
subprocess.run(['scp','-q',HOST+':'+B+'/'+attempt+'-reservation.json',str(P)],check=True)
# Delete only this task’s isolated disposable solver scratch,no keys or shared files.
ssh(f'find {W}/solver-temp -maxdepth 1 -type f \\( -name "external-sat*" -o -name "smt2_dec_problem*" \\) -delete')
sys.exit(r.returncode)
