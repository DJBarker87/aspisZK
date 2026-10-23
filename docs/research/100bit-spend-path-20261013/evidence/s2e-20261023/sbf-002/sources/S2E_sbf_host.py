#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path(__file__).resolve().parent; mode=sys.argv[1];assert mode in ['default','devnet','pool']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((H/'S2E-frozen-sources.json').read_text())
for row in manifest['files']:assert sha(H/'sbf-src'/row['path'])==row['sha256'],row['path']
cache='pool' if mode=='pool' else 'verifier';target=H/('sbf-target-'+cache)
if not target.exists():subprocess.run(['cp','-a','--reflink=auto',str(H.parent/'codex-cx-s10-repin-20261022'/target.name),str(target)],check=True)
for p in (H/'sbf-src').rglob('*.rs'):os.utime(p,None)
manifest_path='programs/aspis-pool' if mode=='pool' else 'programs/r1-cost-probe'
features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if mode=='pool' else 'pool-adapter,private-leaf-salts'
cmd=['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(H/'sbf-src'/manifest_path/'Cargo.toml'),'--sbf-out-dir',str(H/('S2E-artifacts-'+mode)),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_HOME='/home/dombarker/.cargo',CARGO_TARGET_DIR=str(target),CARGO_NET_OFFLINE='true',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4')
for key in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTUP_TOOLCHAIN','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']:env.pop(key,None)
if mode=='devnet':
 ids=json.loads((H/'S2E-devnet-programs.json').read_text())
 env.update(ASPIS_R1_POOL_PROGRAM_ID=ids['pool'],ASPIS_R1_REGISTRY_PROGRAM_ID=ids['registry'])
(H/('S2E-sbf-'+mode+'-command.json')).write_text(json.dumps({'command':cmd,'env':{k:env[k] for k in ['CARGO_TARGET_DIR','CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID'] if k in env},'expected_time':'optimized SBF compilation/linking, copied cache, force own local Rust sources newer; no arithmetic/proof generation'},indent=2)+'\n')
r=subprocess.run(cmd,cwd=H/'sbf-src',env=env)
if r.returncode:raise SystemExit(r.returncode)
name='aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so';p=H/('S2E-artifacts-'+mode)/name
expected={'default':'40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0','devnet':'12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}[mode]
result={'mode':mode,'sha256':sha(p),'bytes':p.stat().st_size,'expected_sha256':expected,'byte_identical':sha(p)==expected,'scope':'fresh build of current branch frozen production file inventory, standalone proof candidate not included in production workspace'}
(H/('S2E-sbf-'+mode+'-pin.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));assert result['byte_identical']
