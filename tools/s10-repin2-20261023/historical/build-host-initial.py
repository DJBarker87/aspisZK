#!/usr/bin/env python3
"""Own copied frozen workspace/cache; capped diagnostics; compare all ELF pins."""
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023')
F=H.parent/'codex-cx-pin-20261020'
K=H.parent/'codex-cx-asq8-kani-20261021/harness'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mode=sys.argv[1]
assert mode in ('default','devnet','pool')
if not (H/'src').exists():shutil.copytree(F/'src',H/'src',symlinks=True)
cache='pool' if mode=='pool' else 'verifier'
target=H/('sbf-target-'+cache)
if not target.exists():subprocess.run(['cp','-a','--reflink=auto',str(H.parent/'codex-cx-s10-inventory3-20261021'/target.name),str(target)],check=True)
# Source paths and diagnostics outputs changed: Cargo must actually recompile
# each selected frozen crate in this private cache, never invalidate shared data.
for p in (H/'src').glob('**/*.rs'):os.utime(p,None)
out=H/('build-'+mode+'-v'+sys.argv[2]);out.mkdir(exist_ok=False)
subprocess.run(['python3',str(K/'reservation.py'),str(out/'reservation.json')],check=True)
manifest='programs/aspis-pool' if mode=='pool' else 'programs/r1-cost-probe'
features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if mode=='pool' else 'pool-adapter,private-leaf-salts'
cmd=['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(H/'src'/manifest/'Cargo.toml'),'--sbf-out-dir',str(out/'artifacts'),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_HOME='/home/dombarker/.cargo',CARGO_TARGET_DIR=str(target),CARGO_NET_OFFLINE='true',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4',RUSTC_WRAPPER=str(H/'rustc-diagnostics.py'),S10_DIAGNOSTICS=str(out/'diagnostics'))
env.pop('RUSTFLAGS',None)
for key in ['ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']:env.pop(key,None)
if mode=='devnet':
    ids=json.loads((F/'r1-devnet.template.json').read_text())['programs']
    env.update(ASPIS_R1_POOL_PROGRAM_ID=ids['pool'],ASPIS_R1_REGISTRY_PROGRAM_ID=ids['registry'])
(out/'command.json').write_text(json.dumps(dict(command=cmd,env={k:env[k] for k in ('CARGO_TARGET_DIR','CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS','RUSTC_WRAPPER','S10_DIAGNOSTICS','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID') if k in env},expected_time='optimized SBF compilation and diagnostic emission; no arithmetic release gate',wrapper_sha256=sha(H/'rustc-diagnostics.py')),indent=2)+'\n')
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(F/'harness/capped.py'),str(out/'receipt'),'optimized frozen SBF compilation with mono/MIR/LLVM diagnostics','--','timeout','600',*cmd]
status=subprocess.run(run,cwd=H/'src',env=env).returncode
if status:raise SystemExit(status)
name='aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so'
artifact=out/'artifacts'/name
expected={'default':'d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0','devnet':'2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}[mode]
shutil.copy2(target/'sbpf-solana-solana/release'/name,out/'linked.elf')
result=dict(mode=mode,sha256=sha(artifact),expected_sha256=expected,bytes=artifact.stat().st_size,byte_identical=sha(artifact)==expected)
(out/'artifact-comparison.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
assert result['byte_identical'],result
# Keep diagnostic files in a per-mode snapshot before the next build overwrites them.
retained=out/'compiler-output';retained.mkdir()
for p in (target/'sbpf-solana-solana/release/deps').iterdir():
 if p.suffix in ('.ll','.mir') and (p.name.startswith(tuple(c+'-' for c in ('aspis_core','aspis_statement','aspis_r1_cost_probe','aspis_r1_cost_probe_program','aspis_pool'))) or p.stem in ('aspis_r1_cost_probe_program','aspis_pool')):shutil.copy2(p,retained/p.name)
