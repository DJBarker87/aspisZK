#!/usr/bin/env python3
"""Stage 0: exact frozen SBF features/toolchain; isolated caches and receipts."""
import os, json, subprocess, time, hashlib
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit29-20261022')
SBF='/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf'
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4')
os.chdir(H/'frozen-src')
expected={'default':'dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34','devnet':'fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
results={}
def reserve(mode):
    while True:
        caps=[]
        for p in Path('/sys/fs/cgroup').rglob('memory.max'):
            try:
                v=p.read_text().strip()
                if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
            except OSError:pass
        if sum(x['bytes'] for x in caps)+8*2**30<=55*2**30:
            (H/('sbf-'+mode+'-reservation.json')).write_text(json.dumps(caps,indent=2)+'\n'); return
        print('SBF reservation hold',flush=True);time.sleep(30)
for mode in ['default','devnet','pool']:
    os.environ['CARGO_TARGET_DIR']=str(H/('sbf-target-pool' if mode=='pool' else 'sbf-target-verifier'))
    for k in ['ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']: os.environ.pop(k,None)
    if mode=='devnet':
        p=json.loads((H/'r1-devnet.template.json').read_text())['programs']
        os.environ.update(ASPIS_R1_POOL_PROGRAM_ID=p['pool'],ASPIS_R1_REGISTRY_PROGRAM_ID=p['registry'])
    out=H/'artifacts'/mode;out.mkdir(parents=True,exist_ok=True)
    package='aspis-pool' if mode=='pool' else 'r1-cost-probe'
    features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if mode=='pool' else 'pool-adapter,private-leaf-salts'
    cmd=['taskset','-c','0-3','env','-u','RUSTFLAGS',SBF,'--manifest-path',str(H/'frozen-src/programs'/package/'Cargo.toml'),'--sbf-out-dir',str(out),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
    reserve(mode)
    subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/('build-'+mode+'-final-owned-sources')),'Incremental optimized SBF compilation/link; no proof generation','--',*cmd],check=True)
    subprocess.run(['sha256sum',str(out/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so'))],check=True)

    elf=out/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so')
    sha=hashlib.sha256(elf.read_bytes()).hexdigest()
    prior=Path('/home/dombarker/project-offloads/codex-cx-prover-commit3-20261020/artifacts')/mode/elf.name
    cmp=subprocess.run(['cmp','--silent',str(elf),str(prior)]).returncode
    results[mode]=dict(sha256=sha,size_bytes=elf.stat().st_size,expected_sha256=expected[mode],cmp_exit=cmp,byte_identical=sha==expected[mode] and cmp==0,receipt=json.loads((H/'receipts'/('build-'+mode+'-final-owned-sources')/'receipt.json').read_text()))
    assert results[mode]['byte_identical'],results[mode]
(H/'frozen-elf-final-check.json').write_text(json.dumps(dict(source_revision=(H/'revision.txt').read_text().strip(),source_hashes={str(p.relative_to(H/'frozen-src')):hashlib.sha256(p.read_bytes()).hexdigest() for p in (H/'frozen-src').rglob('*.rs')},programs=results),indent=2)+'\n')
