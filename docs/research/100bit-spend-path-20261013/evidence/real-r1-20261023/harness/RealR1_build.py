#!/usr/bin/env python3
"""Client fixture and ELF gates in the private pinned workspace; no reruns."""
import hashlib,json,os,subprocess,sys,time
from pathlib import Path
W=Path('/home/dombarker/project-offloads/codex-cx-real-r1-20261023/client')
mode=sys.argv[1]
assert mode in ['native-v1','native-v2','default','devnet','pool']
def reservation():
    caps=[]
    for p in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=p.read_text().strip()
            if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(int(v))
        except OSError:pass
    return sum(caps)
start=time.monotonic()
while reservation()+8*2**30>55*2**30:
    assert time.monotonic()-start<1800
    print('Waiting for 8G host reservation',flush=True);time.sleep(15)
e=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='4',
       RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4')
for k in ['ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID','CARGO_ENCODED_RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER']:e.pop(k,None)
if mode.startswith('native-'):
    e['CARGO_TARGET_DIR']=str(W/'native-target')
    cmd=['cargo','test','--release','--locked','--offline','-j','4','-p','aspis-r1-cost-probe','--features','r1p-check','--lib','RealR1_client::tests','--','--nocapture','--test-threads=1']
    note='Incremental optimized Rust compilation, then two fixture proofs (P_R1 dominates); no dense finite-field gate beyond prover/checker'
else:
    pool=mode=='pool'
    target=W/('sbf-target-pool' if pool else 'sbf-target-verifier')
    if not target.exists():
        cache=Path('/home/dombarker/project-offloads/codex-cx-elf-recheck-20261021')/target.name
        subprocess.run(['cp','-a','--reflink=auto',str(cache),str(target)],check=True)
    e['CARGO_TARGET_DIR']=str(target)
    if mode=='devnet':
        ids=json.loads(Path('/home/dombarker/project-offloads/codex-cx-elf-recheck-20261021/r1-devnet.template.json').read_text())['programs']
        e.update(ASPIS_R1_POOL_PROGRAM_ID=ids['pool'],ASPIS_R1_REGISTRY_PROGRAM_ID=ids['registry'])
    manifest='programs/aspis-pool/Cargo.toml' if pool else 'programs/r1-cost-probe/Cargo.toml'
    features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if pool else 'pool-adapter,private-leaf-salts'
    out=W/'artifacts'/mode;out.mkdir(parents=True,exist_ok=False)
    cmd=['env','-u','RUSTFLAGS','/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf',
         '--manifest-path',str(W/'src'/manifest),'--sbf-out-dir',str(out),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
    note='Incremental optimized SBF compilation/link only; host client feature excluded'
receipt=W/'receipts'/mode
scope=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64',
       'python3',str(W.parent/'harness/RealR1_capped.py'),str(receipt),note,'--',*cmd]
status=subprocess.run(scope,cwd=W/'src',env=e).returncode
if status:raise SystemExit(status)
if not mode.startswith('native-'):
    artifact=out/('aspis_pool.so' if pool else 'aspis_r1_cost_probe_program.so')
    sha=hashlib.sha256(artifact.read_bytes()).hexdigest()
    expected={'default':'40dc7574','devnet':'12cb0bc2','pool':'121f3e29'}[mode]
    record=dict(mode=mode,sha256=sha,bytes=artifact.stat().st_size,expected_prefix=expected,match=sha.startswith(expected))
    (receipt/'artifact.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
    assert record['match'],record
