"""Configure the unchanged admitted S2W runner; one proof scope per invocation."""
from pathlib import Path
import subprocess,json,time,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-3-20261027'
a,kind,target=sys.argv[1:]
def ssh(s):return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def collect(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
if (E/a/'receipt.json').exists():raise SystemExit('Refuse existing attempt')
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
cfg=dict(attempt=a,kind=kind,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,reservation_retries=retry)
if kind=='kani':
 cfg.update(sources=['LPc_src/Cargo.toml','LPc_src/Cargo.lock']+['LPc_src/'+p for p in json.loads((E/'LPc_sources.json').read_text())],command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/LPc_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/LPc_target','--lib','-j','1','-Z','unstable-options','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse'],deps_fingerprint={'release_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','source_manifest':'LPc_source-provenance.json','boundary':'scratch frozen source plus LPa and LPc cfg-only harness patches'},expected_time='optimized Kani compilation then bounded native stage '+target,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=1'})
else:
 src=('LPc_inherited/' if kind=='inherited' else 'LPc_generated/')+target+'.lean';obj='LPc_objects/'+target+'.olean'
 cfg['kind']='lean'
 cfg.update(module=target,sources=[src],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R',('LPc_inherited' if kind=='inherited' else 'LPc_generated'),'-o',obj,src],env={'LEAN_PATH':B+'/LPc_objects:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'},deps_fingerprint={'scope':'coherent SInt2 objects plus LPc new modules'},expected_time='single symbolic module; no concrete large numeral normalization')
 r=ssh(f'mkdir -p {B}/LPc_generated {B}/LPc_objects');assert r.returncode==0,r.stderr
 if kind!='inherited':subprocess.run(['scp','-q',str(E/(target+'.lean')),H+':'+B+'/'+src],check=True)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run(['scp','-q',str(E/(a+'.json')),H+':'+B+'/'+a+'.json'],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 {('S2W_run_host.py' if kind=='kani' else 'S2W_lean_host.py')} {a}.json')
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
rc=json.loads((E/a/'receipt.json').read_text());print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','print_axioms']}),flush=True)
print((E/a/'stdout.log').read_text()[-5000:],flush=True)
