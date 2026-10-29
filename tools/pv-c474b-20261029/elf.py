"""One optimized frozen-ELF rebuild; invoked inside the capped scope."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');R=H/'src';mode=sys.argv[1];out=H/'bundle'/('elf-'+mode);out.mkdir(exist_ok=False)
pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/('sbf-target-pool' if mode=='pool' else 'sbf-target-verifier')),CARGO_NET_OFFLINE='true',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4')
for key in ['RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']:env.pop(key,None)
if mode=='devnet':env.update(ASPIS_R1_POOL_PROGRAM_ID='BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs',ASPIS_R1_REGISTRY_PROGRAM_ID='9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q')
program='aspis-pool' if mode=='pool' else 'r1-cost-probe'
features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if mode=='pool' else 'pool-adapter,private-leaf-salts'
cmd=['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(R/'programs'/program/'Cargo.toml'),'--sbf-out-dir',str(out),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
(out/'command.json').write_text(json.dumps(dict(command=cmd,environment={k:v for k,v in env.items() if k.startswith(('CARGO','RUST','ASPIS'))},expected_phase='optimized SBF compilation/link; no proof generation'),indent=2)+'\n')
status=subprocess.run(cmd,cwd=R,env=env).returncode
for k in out.glob('*keypair.json'):k.chmod(0o600)
a=out/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so')
r=dict(mode=mode,exit=status,expected=pins[mode])
if a.exists():r.update(sha256=hashlib.sha256(a.read_bytes()).hexdigest(),bytes=a.stat().st_size)
r['byte_identical']=r.get('sha256')==r['expected'];(out/'comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
sys.exit(status or (0 if r['byte_identical'] else 2))
