"""Orchestration only; unchanged S2W runner and reservation barrier."""
from pathlib import Path
import subprocess,json,sys,time,hashlib
P=Path(__file__).resolve().parent; R=P.parents[1]; HOST='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-finish-pair2-20261027'
def ssh(c,**k):return subprocess.run(['ssh',HOST,c],**k)
n=int(sys.argv[1]);h=sys.argv[2];assert 1<=n<=20
a=f'FJd_K{n:03}';assert not (P/a).exists()
ssh(f'mkdir -p {B}; cp -n /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S2W_run_host.py {B}/',check=True)
cfg=dict(attempt=a,kind='kani',command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path','FJd_harness/Cargo.toml','--target-dir','FJd_target','-j','4','--exact','--harness','weights::FJd_Loops::'+h,'--no-assertion-reach-checks','--no-overflow-checks','--output-format','terse'],timeout=180,sources=[str(p.relative_to(P)) for p in (P/'FJd_harness').rglob('*') if p.is_file() and p.name!='Cargo.lock'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'4','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_NET_OFFLINE':'true'},deps_fingerprint={'shipped_weights_sha256':hashlib.sha256((R/'crates/aspis-r1-cost-probe/src/weights.rs').read_bytes()).hexdigest(),'corpus':'read-only /home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src'},expected_time='Optimized compilation then bounded '+h+' equality; no stubs; no dense elimination')
(P/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
for retry in range(11):
 r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier.log 2>&1; reservation_status=$?; cat {B}/{a}-barrier.log; exit $reservation_status',capture_output=True,text=True)
 (P/(a+'-barrier.log')).write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode==78 and retry<10:print('Reservation busy; wait 180s',flush=True);time.sleep(180);continue
 if retry==0 and ('FileNotFoundError' in r.stdout+r.stderr or not r.stdout.strip()):time.sleep(30);continue
 sys.exit(r.returncode)
subprocess.run(['scp','-qr',str(P/'FJd_harness'),str(P/(a+'.json')),HOST+':'+B+'/'],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json',capture_output=True,text=True);print(r.stdout+r.stderr)
subprocess.run(['scp','-qr',HOST+':'+B+'/'+a,str(P)],check=True)
subprocess.run(['scp','-q',HOST+':'+B+'/'+a+'-reservation.json',str(P)],check=True)
sys.exit(r.returncode)
