"""Serial job orchestration with unchanged S2H admission and S2W runner."""
from pathlib import Path
import subprocess,json,time,hashlib,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-1-20261027'
def ssh(s):return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def collect(n):subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
ns=['compact::LPa_compact::LPa_check_stage', 'compact::LPa_compact::LPa_check_composition', 'compact::LPa_compact::LPa_check_tail', 'compact::LPa_compact::LPa_expand_stage', 'compact::LPa_compact::LPa_expand_alignment', 'compact::LPa_compact::LPa_expand_indexed_stage', 'compact::LPa_compact::LPa_expand_length', 'verifier::LPa_verifier::LPa_echeck_stage', 'verifier::LPa_verifier::LPa_echeck_tail', 'verifier::LPa_verifier::LPa_echeck_composition', 'r1_wire::LPa_wire::LPa_decode_stage', 'r1_wire::LPa_wire::LPa_decode_guard29', 'r1_wire::LPa_wire::LPa_validate_stage', 'r1_wire::LPa_wire::LPa_validate_composition', 'verifier::candidate::LPa_candidate::LPa_view_inactive', 'r1_semantic::LPa_semantic::LPa_boundary', 'fast_pairing::canonical::LPa_dot::LPa_dot_stage', 'sampler::LPa_sampler::LPa_circle_fallback', 'r1_semantic::LPa_semantic::LPa_claim_point0', 'r1_semantic::LPa_semantic::LPa_boundary_step']
for i,n in enumerate(ns,1):
 if len(sys.argv)>1 and i not in [int(a) for a in sys.argv[1:]]:continue
 a=f'LPa_K{i:03}'
 prior=len(list(E.glob(a+'-barrier-*.log')))
 for retry in range(prior,11):
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
 sources=['LPa_src/Cargo.toml','LPa_src/Cargo.lock']+['LPa_src/'+p for p in json.loads((E/'LPa_sources.json').read_text())]
 cfg=dict(attempt=a,kind='kani',sources=sources,command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/LPa_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/LPa_target','--lib','-j','1','-Z','unstable-options','--harness-timeout','90s','--exact','--harness',n,'--output-format','terse'],timeout=180,source_revision=rev,source_tree_dirty=True,deps_fingerprint={'release_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','boundary':'direct shipped-library stage calls; exact domain documented per harness'},expected_time='Optimized Kani compilation followed by one named bounded boundary stage '+n,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=1'},reservation_retries=retry)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 subprocess.run(['scp','-q',*[str(Path(f.removeprefix('LPa_src/'))) for f in sources if f.endswith('.rs')],H+':'+B+'/LPa_src/crates/aspis-r1-cost-probe/src/'],check=True)
 subprocess.run(['scp','-q',str(E/(a+'.json')),H+':'+B+'/'+a+'.json'],check=True)
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json')
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 (E/a).mkdir(exist_ok=True)
 for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
 # Keep exact compiler input snapshots for every source in the run receipt.
 for f in sources:
  q=E/a/'sources'/f;q.parent.mkdir(parents=True,exist_ok=True)
  local=Path(f.removeprefix('LPa_src/'));q.write_bytes(local.read_bytes())
 rc=json.loads((E/a/'receipt.json').read_text());print(a,rc['exit_status'],rc['wall_seconds'],rc['peak_rss_kib'],flush=True)
 if rc['exit_status']!=0:
  print((E/a/'stdout.log').read_text()[-2500:],flush=True)
  if rc['exit_status'] in [124,137]:
   print('No unchanged retry; independent next harness only',flush=True)

 # Failed/timed-out shapes are retained and never retried unchanged.
