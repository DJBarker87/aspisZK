#!/usr/bin/env python3
"""Run selected-module probes sequentially against the read-only frozen copy."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory2-20261021')
F=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory-20261021')
K=Path('/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021/harness')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,crate,module,features in [
    (a.split(':')[0], a.split(':')[1], a.split(':')[2], a.split(':')[3]) for a in sys.argv[1:]
]:
    out=H/name;out.mkdir(exist_ok=False)
    with (out/'reservation.log').open('w') as log:
        subprocess.run(['python3',str(K/'reservation.py'),str(out/'reservation.json')],stdout=log,check=True)
    manifest={'aspis_pool':'programs/aspis-pool','aspis_r1_cost_probe_program':'programs/r1-cost-probe',
              'aspis_r1_cost_probe':'crates/aspis-r1-cost-probe','aspis_core':'crates/aspis-core',
              'aspis_statement':'crates/aspis-statement'}[crate]
    env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
        CARGO_TARGET_DIR=str(F/'charon-target'),CARGO_BUILD_JOBS='1',
        RUSTFLAGS='-C link-arg=-Wl,--threads=4 --cfg target_os="solana" -Aexplicit_builtin_cfgs_in_flags',
        RUSTC_WORKSPACE_WRAPPER=str(H/'mir-edges'),S10_MODULE=module,S10_CRATE=crate,
        S10_OUTPUT=str(out/'mir.tsv'))
    cmd=['/home/dombarker/.cargo/bin/cargo','+nightly-2026-06-01','rustc',
        '--manifest-path',str(F/'src'/manifest/'Cargo.toml'),'--locked','--offline','--release',
        '--lib','--target','x86_64-unknown-linux-gnu','-j','1']
    if features:cmd+=['--features',features]
    cmd+=['--','--cfg',name.replace('-','_')]
    (out/'command.json').write_text(json.dumps(dict(command=cmd,env={k:env[k] for k in ['S10_MODULE','S10_CRATE','RUSTFLAGS','CARGO_TARGET_DIR']},
        source_revision='b2727acd3abf79315d18b754a260f58f4b1c6326',driver_sha256=sha(H/'mir_edges.rs'),
        expected_time='optimized dependency compilation if needed, then selected module MIR queries; no whole Pool graph'),indent=2)+'\n')
    run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G',
         '-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(K/'capped.py'),str(out/'receipt'),
         'Optimized dependency compilation then one selected module MIR visit; 600 second no-progress ceiling',
         '--','timeout','600',*cmd]
    with (out/'launch.log').open('w') as log:
        status=subprocess.run(run,cwd=F/'src',env=env,stdout=log,stderr=subprocess.STDOUT).returncode
    print(name,status, 'bytes', (out/'mir.tsv').stat().st_size if (out/'mir.tsv').exists() else None,flush=True)
    if status:break
