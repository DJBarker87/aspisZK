#!/usr/bin/env python3
"""Host-only exact-source ELF identity; one capped scope per build."""
import hashlib, json, os, pathlib, shutil, subprocess, time
R = pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref8-20261021/stage0')
F = pathlib.Path('/home/dombarker/project-offloads/codex-cx-pin-20261020')
S = R/'src'
revision = os.environ.get('SOURCE_REVISION', '03a65e8cf + retained source pins')
suffix = os.environ.get('RECEIPT_SUFFIX', '')
env = os.environ.copy()
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', CARGO_NET_OFFLINE='true',
           RUSTFLAGS='-C link-arg=-Wl,--threads=4',
           CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4')
for key in ['ASPIS_R1_POOL_PROGRAM_ID', 'ASPIS_R1_REGISTRY_PROGRAM_ID']:
    env.pop(key, None)
sol = '/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf'
# Isolated cache copies: never write the frozen build workspace.
for name in ['verifier', 'pool']:
    dst = R/('sbf-target-'+name)
    if not dst.exists():
        subprocess.run(['cp','-a','--reflink=auto',str(F/dst.name),str(dst)],check=True)
cap = (F/'harness/capped.py').read_text().replace("Path('/home/dombarker/project-offloads/codex-cx-pin-20261020/source-revision.txt').read_text().strip()", repr(revision))
(R/'capped.py').write_text(cap)
for mode, target, manifest, features, artifact in [
    ('default','verifier','r1-cost-probe','pool-adapter,private-leaf-salts','aspis_r1_cost_probe_program.so'),
    ('devnet','verifier','r1-cost-probe','pool-adapter,private-leaf-salts','aspis_r1_cost_probe_program.so'),
    ('pool','pool','aspis-pool','r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit','aspis_pool.so')]:
    while True:
        reserved = 0
        for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
            try:
                v=p.read_text().strip()
                if v!='max' and (p.parent/'cgroup.procs').read_text().strip(): reserved+=int(v)
            except OSError: pass
        if reserved+8*2**30<=55*2**30: break
        print(mode, 'waiting for 8 GiB reservation:', reserved, flush=True)
        time.sleep(20)
    e = env.copy()
    if mode=='devnet':
        ids=json.loads((F/'r1-devnet.template.json').read_text())['programs']
        e.update(ASPIS_R1_POOL_PROGRAM_ID=ids['pool'],ASPIS_R1_REGISTRY_PROGRAM_ID=ids['registry'])
    e['CARGO_TARGET_DIR']=str(R/('sbf-target-'+target))
    out=R/'artifacts'/mode; out.mkdir(parents=True,exist_ok=True)
    command=['env','-u','RUSTFLAGS',sol,'--manifest-path',str(S/'programs'/manifest/'Cargo.toml'),
             '--sbf-out-dir',str(out),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
    print(mode,'reserved bytes',reserved,'expected time: optimized SBF compilation/link',flush=True)
    subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G',
                    '-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'capped.py'),str(R/'receipts'/(mode+suffix)),
                    'Optimized SBF compilation/link; no proof generation','--',*command],cwd=S,env=e,check=True)
    data=(out/artifact).read_bytes()
    receipt=json.loads((R/'receipts'/(mode+suffix)/'receipt.json').read_text())
    receipt.update(artifact_sha256=hashlib.sha256(data).hexdigest(),artifact_size=len(data),reservation_before_bytes=reserved,
                   build_environment={k:e.get(k) for k in ['RUSTFLAGS','CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']})
    (R/'receipts'/(mode+suffix)/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(mode, receipt['artifact_sha256'],flush=True)
