from run import H,run
import json,hashlib,sys,os
S=H/'source'
pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
for mode in ['default','devnet','pool']:
 label=sys.argv[1]+'-'+mode
 out=H/label/'artifacts';program='aspis-pool' if mode=='pool' else 'r1-cost-probe'
 features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if mode=='pool' else 'pool-adapter,private-leaf-salts'
 env={'CARGO_HOME':'/home/dombarker/.cargo','CARGO_TARGET_DIR':str(H/'sbf-target'),'CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS':'-C link-arg=--threads=4','RUSTC_WRAPPER':'/home/dombarker/project-offloads/codex-cx-lowering2-20261026/rustc-diagnostics.py','S10_DIAGNOSTICS':str(H/label/'diagnostics')}
 if mode=='devnet':env.update(ASPIS_R1_POOL_PROGRAM_ID='BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs',ASPIS_R1_REGISTRY_PROGRAM_ID='9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q')
 cmd=['timeout','600','/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(S/'programs'/program/'Cargo.toml'),'--sbf-out-dir',str(out),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
 status=run(label,cmd,'optimized SBF compilation and diagnostic emission; no arithmetic elimination',env)
 if status:sys.exit(status)
 file=out/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so')
 actual=hashlib.sha256(file.read_bytes()).hexdigest();rec=dict(file=str(file),sha256=actual,expected=pins[mode],bytes=file.stat().st_size,match=actual==pins[mode]);(H/label/'pin.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
 if actual!=pins[mode]:sys.exit('ELF MISMATCH: '+str(file))
