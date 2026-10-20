#!/usr/bin/env python3
"""Capture the frozen-program resolved normal/build dependency inventories."""
import json, os, subprocess, hashlib
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit3-20261020')
os.chdir(H/'src')
os.environ.update(PATH='/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin:/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTC='/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/rustc',CARGO_NET_OFFLINE='true')
records={}
for mode in ['default','devnet','pool']:
    package='aspis-pool' if mode=='pool' else 'aspis-r1-cost-probe-program'
    features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if mode=='pool' else 'pool-adapter,private-leaf-salts'
    cmd=['cargo','tree','--locked','--offline','-p',package,'--features',features,'--target','sbpf-solana-solana','--edges','normal,build','--prefix','none','--format','{p} features=[{f}]','--no-dedupe']
    p=subprocess.run(cmd,text=True,capture_output=True)
    records[mode]={'command':cmd,'exit':p.returncode,'stderr':p.stderr,'crates':sorted(set(p.stdout.splitlines()))}
(H/'dependency-inventory.json').write_text(json.dumps(records,indent=2)+'\n')
print({k:(v['exit'],len(v['crates'])) for k,v in records.items()})
