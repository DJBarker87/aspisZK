"""Use the unchanged S2W command runner for the owner-required ELF pin gate."""
from pathlib import Path
import json,subprocess,sys,time
P=Path(__file__).resolve().parent;R=P.parents[1]
HOST='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-finish-pair2-20261027'
S='/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src'
mode=sys.argv[1];assert mode in ['default','devnet','pool'];a='FJd_SBF_'+mode+('_wrapper' if len(sys.argv)>2 else '');assert not (P/a).exists()
def ssh(c,**k):return subprocess.run(['ssh',HOST,c],**k)
features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if mode=='pool' else 'pool-adapter,private-leaf-salts'
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_HOME='/home/dombarker/.cargo',CARGO_TARGET_DIR=B+'/FJd_sbf_target',CARGO_NET_OFFLINE='true',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4',CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL='3')
if len(sys.argv)>2:env.update(RUSTC_WRAPPER='/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/rustc-diagnostics.py',S10_DIAGNOSTICS=B+'/'+a+'_diagnostics')
if mode=='devnet':env.update(ASPIS_R1_POOL_PROGRAM_ID='BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs',ASPIS_R1_REGISTRY_PROGRAM_ID='9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q')
cfg=dict(attempt=a,kind='sbf',sources=['FJd_harness/src/FJd_Loops.rs'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,command=['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',S+('/programs/aspis-pool/Cargo.toml' if mode=='pool' else '/programs/r1-cost-probe/Cargo.toml'),'--sbf-out-dir',B+'/FJd_artifacts_'+mode,'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked'],timeout=600,env=env,deps_fingerprint={'corpus':S,'reference_recipe':'tools/s10-repin3-20261023/build-host.py; own outputs and optimized build scripts'},expected_time='Optimized SBF compilation; build-script circle table generation uses opt3; no Lean/Kani/elimination')
(P/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
for retry in range(11):
 r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier.log 2>&1; reservation_status=$?; cat {B}/{a}-barrier.log; exit $reservation_status',capture_output=True,text=True)
 (P/(a+'-barrier.log')).write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode==78 and retry<10:print('Reservation busy; wait 180s',flush=True);time.sleep(180);continue
 if retry==0 and 'FileNotFoundError' in r.stdout+r.stderr:time.sleep(30);continue
 sys.exit(r.returncode)
subprocess.run(['scp','-q',str(P/(a+'.json')),HOST+':'+B+'/'],check=True)
r=ssh(f'cd {B} && env -u RUSTFLAGS -u ASPIS_R1_POOL_PROGRAM_ID -u ASPIS_R1_REGISTRY_PROGRAM_ID systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json',capture_output=True,text=True);print(r.stdout+r.stderr)
subprocess.run(['scp','-qr',HOST+':'+B+'/'+a,str(P)],check=True)
subprocess.run(['scp','-q',HOST+':'+B+'/'+a+'-reservation.json',str(P)],check=True)
if r.returncode:sys.exit(r.returncode)
name='aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so'
check=ssh(f'sha256sum {B}/FJd_artifacts_{mode}/{name}; stat -c %s {B}/FJd_artifacts_{mode}/{name}',capture_output=True,text=True)
(P/(a+'-pin.txt')).write_text(check.stdout+check.stderr);print(check.stdout+check.stderr)
sys.exit(check.returncode)
