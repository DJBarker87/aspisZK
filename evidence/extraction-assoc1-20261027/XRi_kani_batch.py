"""Serial job orchestration with unchanged S2H admission and S2W runner."""
from pathlib import Path
import subprocess,json,time,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-extraction-assoc1-20261027'
def ssh(s):return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def collect(n):subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
ns=['powers29_zero','powers29_one','powers7_zero','powers7_one','prepared_zero','prepared_one','checkpoint_pair','checkpoint_four','checkpoint_e_pair','checkpoint_zero_weights']
for i,n in enumerate(ns,1):
 a=f'XRi_K{i:03}'
 for retry in range(11):
  log=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');collect(log)
  exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
  if not exists and retry==0:time.sleep(30);continue
  if exists:
   collect(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
   if r.returncode==0 and ad['allowed']:break
   if (r.returncode==78 or 'quiet window' in ad.get('reason','')) and retry<10:print(a,'reservation wait',flush=True);time.sleep(180);continue
  if 'FileNotFoundError' in (E/log).read_text() and retry==0:time.sleep(30);continue
  raise SystemExit('STOP admission '+r.stdout+r.stderr)
 else:raise SystemExit('STOP reservation retries')
 sources=['XRi_Cargo.toml','XRi_lib.rs','XRi_actual.rs','XRi_reference.rs','XRi_harnesses.rs']
 cfg=dict(attempt=a,kind='kani',sources=sources,command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/XRi_crate/Cargo.toml','--target-dir',B+'/XRi_target','-j','1','-Z','unstable-options','--harness-timeout','90s','--exact','--harness','XRi_harnesses::XRi_'+n,'--output-format','terse'],timeout=180,source_revision=rev,source_tree_dirty=True,deps_fingerprint={'release_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','boundary':'new sparse prepared_claim/powers or split checkpoint source stages; whole P6 open'},expected_time='Optimized Kani compilation followed by one named bounded boundary stage '+n,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=1'},reservation_retries=retry)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 for f in [a+'.json',*sources]:subprocess.run(['scp','-q',str(E/f),H+':'+B+'/'+f],check=True)
 if i==1:
  r=ssh('mkdir -p '+B+'/XRi_crate');assert r.returncode==0
  for f in sources:
   name='Cargo.toml' if f=='XRi_Cargo.toml' else f
   r=ssh(f'ln -s ../{f} {B}/XRi_crate/{name}');assert r.returncode==0,r.stderr
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json')
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 (E/a).mkdir(exist_ok=True)
 for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
 rc=json.loads((E/a/'receipt.json').read_text());print(a,rc['exit_status'],rc['wall_seconds'],rc['peak_rss_kib'],flush=True)
 if rc['exit_status']!=0:
  print((E/a/'stdout.log').read_text()[-2500:],flush=True)
  if rc['exit_status'] in [124,137]:
   print('No unchanged retry; independent next harness only',flush=True)
