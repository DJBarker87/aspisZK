#!/usr/bin/env python3
"""Stage 0: exact frozen SBF features/toolchain; isolated caches and receipts."""
import os, json, subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit3-20261020')
SBF='/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf'
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4')
os.chdir(H/'src')
for mode in ['default','devnet','pool']:
    os.environ['CARGO_TARGET_DIR']=str(H/('sbf-target-pool' if mode=='pool' else 'sbf-target-verifier'))
    for k in ['ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']: os.environ.pop(k,None)
    if mode=='devnet':
        p=json.loads((H/'r1-devnet.template.json').read_text())['programs']
        os.environ.update(ASPIS_R1_POOL_PROGRAM_ID=p['pool'],ASPIS_R1_REGISTRY_PROGRAM_ID=p['registry'])
    out=H/'artifacts'/mode;out.mkdir(parents=True,exist_ok=True)
    package='aspis-pool' if mode=='pool' else 'r1-cost-probe'
    features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if mode=='pool' else 'pool-adapter,private-leaf-salts'
    cmd=['env','-u','RUSTFLAGS',SBF,'--manifest-path',str(H/'src/programs'/package/'Cargo.toml'),'--sbf-out-dir',str(out),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
    subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/('build-'+mode)),'Incremental optimized SBF compilation/link; no proof generation','--',*cmd],check=True)
    subprocess.run(['sha256sum',str(out/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so'))],check=True)
