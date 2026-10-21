from pathlib import Path
import os, subprocess, json, hashlib, time

H = Path('/home/dombarker/project-offloads/codex-cx-elf-recheck-20261021')
F = Path('/home/dombarker/project-offloads/codex-cx-pin-20261020')
env = dict(os.environ, PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
           CARGO_HOME='/home/dombarker/.cargo', CARGO_NET_OFFLINE='true',
           RUSTFLAGS='-C link-arg=-Wl,--threads=4',
           CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4')
for k in ['ASPIS_R1_POOL_PROGRAM_ID', 'ASPIS_R1_REGISTRY_PROGRAM_ID', 'CARGO_ENCODED_RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER']:
    env.pop(k, None)
ids = json.loads((H/'r1-devnet.template.json').read_text())['programs']
results = []
for mode in ['default', 'devnet', 'pool']:
    pool = mode == 'pool'
    target = 'sbf-target-pool' if pool else 'sbf-target-verifier'
    e = dict(env, CARGO_TARGET_DIR=str(H/target))
    if mode == 'devnet':
        e.update(ASPIS_R1_POOL_PROGRAM_ID=ids['pool'], ASPIS_R1_REGISTRY_PROGRAM_ID=ids['registry'])
    manifest = 'programs/aspis-pool/Cargo.toml' if pool else 'programs/r1-cost-probe/Cargo.toml'
    features = 'r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit' if pool else 'pool-adapter,private-leaf-salts'
    artifact = 'aspis_pool.so' if pool else 'aspis_r1_cost_probe_program.so'
    out = H/'artifacts'/mode
    out.mkdir(parents=True)
    cmd = ['env', '-u', 'RUSTFLAGS', '/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf',
           '--manifest-path', str(H/'src'/manifest), '--sbf-out-dir', str(out), '--features', features,
           '--skip-tools-install', '--offline', '-j', '4', '--', '--locked']
    scope = ['systemd-run', '--user', '--scope', '--unit=cx-elf-recheck-'+mode+'-20261021', '-q',
             '-p', 'MemoryHigh=6G', '-p', 'MemoryMax=8G', '-p', 'MemorySwapMax=0', '-p', 'TasksMax=64',
             'python3', str(H/'capped.py'), str(H/'receipts'/mode),
             'Incremental optimized SBF compilation/link; no arithmetic execution or proof generation', '--', *cmd]
    print('START', mode, time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), flush=True)
    p = subprocess.Popen(scope, cwd=H/'src', env=e)
    while p.poll() is None:
        time.sleep(15)
        log = H/'receipts'/mode/'stderr.log'
        if log.exists():
            print(mode, 'progress:', log.stat().st_size, 'stderr bytes;', log.read_text(errors='replace').splitlines()[-1:], flush=True)
    if p.returncode:
        raise SystemExit(p.returncode)
    receipt = H/'receipts'/mode
    (receipt/'environment.json').write_text(json.dumps({k:v for k,v in e.items() if k in ['RUSTFLAGS','CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS','CARGO_TARGET_DIR','CARGO_NET_OFFLINE','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID','PATH','CARGO_HOME']}, indent=2)+'\n')
    (receipt/'linked-copy.log').write_text(subprocess.check_output(['cp', str(H/target/'sbpf-solana-solana/release'/artifact), str(out/'linked.elf')], text=True))
    for name in [artifact, 'linked.elf']:
        old, new = F/'artifacts'/mode/name, out/name
        cmp = subprocess.run(['cmp', str(old), str(new)], capture_output=True, text=True)
        result = dict(program=mode, artifact=name, frozen_path=str(old), rebuilt_path=str(new),
                      frozen_sha256=hashlib.sha256(old.read_bytes()).hexdigest(), rebuilt_sha256=hashlib.sha256(new.read_bytes()).hexdigest(),
                      bytes=new.stat().st_size, cmp_command=['cmp',str(old),str(new)], cmp_exit_status=cmp.returncode,
                      cmp_stdout=cmp.stdout, cmp_stderr=cmp.stderr, result='MATCH' if cmp.returncode==0 else 'MISMATCH')
        results.append(result)
        print(json.dumps(result), flush=True)
    sha = subprocess.check_output(['sha256sum', str(F/'artifacts'/mode/artifact), str(out/artifact), str(F/'artifacts'/mode/'linked.elf'), str(out/'linked.elf')], text=True)
    (receipt/'sha256sum.txt').write_text(sha)
    (H/'comparisons.json').write_text(json.dumps(results, indent=2)+'\n')
print('DONE', flush=True)
