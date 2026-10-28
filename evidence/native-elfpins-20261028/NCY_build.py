from pathlib import Path
import os,sys,json,subprocess,hashlib,time
H=Path('/home/dombarker/project-offloads/codex-cx-native-elfpins-20261028')
F=H.parent/'codex-cx-lowering2-20261026'
mode=sys.argv[1] if len(sys.argv)>1 else MODE
assert mode in ('devnet','pool')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((H/'NCY_SOURCE_PINS.json').read_text())
S=H/'NCY_src'
if not S.exists():subprocess.run(['cp','-a',str(F/'src'),str(S)],check=True)
def check():
 bad=[n for n,h in pins['files'].items() if not (S/n).is_file() or sha(S/n)!=h]
 assert not bad,bad
 return {'files':len(pins['files']),'mismatches':bad}
pre=check()
# Own warm SBF cache; never invalidate or write the source cache.
target=H/('NCY_target_'+mode)
assert not target.exists()
seed=F/('sbf-target-pool' if mode=='pool' else 'sbf-target-verifier')
subprocess.run(['cp','-a','--reflink=auto',str(seed),str(target)],check=True)
# Changing private source mtimes ensures selected repository crates compile again.
for p in S.rglob('*.rs'):os.utime(p,None)
out=H/('NCY_B001' if mode=='devnet' else 'NCY_B002');out.mkdir(exist_ok=False)
(out/'artifacts').mkdir();(out/'diagnostics').mkdir()
compiler=Path('/home/dombarker/.rustup/toolchains/1.89.0-sbpf-solana-v1.52/bin/rustc')
tool=Path('/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf')
assert sha(tool)=='46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c'
assert sha(compiler)=='d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002'
wrapper=F/'rustc-diagnostics.py'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_HOME='/home/dombarker/.cargo',CARGO_TARGET_DIR=str(target),CARGO_NET_OFFLINE='true',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4',RUSTC_WRAPPER=str(wrapper),S10_DIAGNOSTICS=str(out/'diagnostics'))
for k in ['RUSTFLAGS','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS']:env.pop(k,None)
if mode=='devnet':env.update(ASPIS_R1_POOL_PROGRAM_ID='BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs',ASPIS_R1_REGISTRY_PROGRAM_ID='9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q')
features='pool-adapter,private-leaf-salts' if mode=='devnet' else 'r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit'
manifest=S/('programs/r1-cost-probe/Cargo.toml' if mode=='devnet' else 'programs/aspis-pool/Cargo.toml')
cmd=[str(tool),'--manifest-path',str(manifest),'--sbf-out-dir',str(out/'artifacts'),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
record={'mode':mode,'phase':'optimized release SBF compilation and linking; no arithmetic gate or proof generation','command':cmd,'cwd':str(S),'frozen_revision':pins['frozen_revision'],'source_check_before':pre,'source_pin_manifest_sha256':sha(H/'NCY_SOURCE_PINS.json'),'cache_seed':str(seed),'wrapper_sha256':sha(wrapper),'compiler_sha256':sha(compiler),'cargo_build_sbf_sha256':sha(tool),'environment':{k:env[k] for k in ['PATH','CARGO_HOME','CARGO_TARGET_DIR','CARGO_NET_OFFLINE','CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS','RUSTC_WRAPPER','S10_DIAGNOSTICS','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID'] if k in env},'unset':['RUSTFLAGS','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS']}
(out/'command.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record),flush=True)
t0=time.monotonic();r=subprocess.run(cmd,cwd=S,env=env);duration=time.monotonic()-t0
post=check()
a=out/'artifacts'/('aspis_r1_cost_probe_program.so' if mode=='devnet' else 'aspis_pool.so')
expected='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299' if mode=='devnet' else '121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'
# Retain any generated key securely, without reading or destroying it.
keys=[]
for p in (out/'artifacts').glob('*keypair*'):
 p.chmod(0o600);keys.append({'path':str(p),'mode':oct(p.stat().st_mode & 0o777),'retained':True})
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().split('0::',1)[1].strip().lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert list(limits.values())==['6442450944','8589934592','0','64'],limits
result={'mode':mode,'build_exit':r.returncode,'build_wall_seconds':duration,'artifact_sha256':sha(a) if a.exists() else None,'expected_sha256':expected,'bytes':a.stat().st_size if a.exists() else None,'source_check_after':post,'print_axioms':'N/A: no Lean theorem','limits':limits,'cgroup_memory_peak_bytes':(cg/'memory.peak').read_text().strip(),'cgroup_swap_peak_bytes':(cg/'memory.swap.peak').read_text().strip(),'keys':keys}
result['match']=result['artifact_sha256']==expected
(out/'artifact.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
assert r.returncode==0 and result['match'],result
