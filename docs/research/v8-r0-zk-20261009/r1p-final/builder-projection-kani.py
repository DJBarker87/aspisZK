#!/usr/bin/env python3
"""Host-only bounded projection proofs. A timeout requires decomposition."""
import hashlib, json, os, pathlib, subprocess, sys, time
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref2-20261021')
S=R/'source'
env=os.environ.copy()
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
for h in sys.argv[1:]:
    while True:
        reserved=0
        for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
            try:
                v=p.read_text().strip()
                if v!='max' and (p.parent/'cgroup.procs').read_text().strip():reserved+=int(v)
            except OSError:pass
        if reserved+8*2**30<=55*2**30: break
        (R/'continuation3').mkdir(exist_ok=True)
        with (R/'continuation3/reservation-waits.jsonl').open('a') as f: f.write(json.dumps(dict(harness=h,reserved_bytes=reserved,time=time.time()))+'\n')
        print(h, 'waiting for 8 GiB reservation:', reserved, flush=True)
        time.sleep(20)
    # Solver work, no arithmetic release gate. Compile in Kani's proof profile.
    cmd=['cargo','kani','-Z','stubbing','-Z','unstable-options','-p','aspis-statement','--lib','-j','4',
         '--output-format','terse','--harness',h,'--cbmc-args','--unwinding-assertions']
    receipt=R/'continuation3'/h
    print(h,'expected time: proof compilation and one named CBMC projection; reserved',reserved,flush=True)
    cap=(R/'stage0/capped.py').read_text().replace("'df54ab57e'", "'3db338587 + proof-only source pins'")
    (R/'continuation3').mkdir(exist_ok=True)
    (R/'continuation3/capped.py').write_text(cap)
    pins = {str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest()
            for root in ['crates/aspis-core','crates/aspis-statement','tools/r1-builder-reference',
                         'docs/research/v8-r0-zk-20261009/refine/writers',
                         'docs/research/v8-r0-zk-20261009/refine/blockwriters',
                         'docs/research/v8-r0-zk-20261009/refine/poseidon']
            for p in (S/root).rglob('*') if p.is_file() and p.suffix in ['.rs','.toml']}
    status=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G',
        '-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'continuation3/capped.py'),str(receipt),
        'Proof compilation then bounded CBMC '+h,'--','timeout','120',*cmd],cwd=S,env=env).returncode
    (receipt/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
    print(h,'exit',status,flush=True)
    print((receipt/'stdout.log').read_text()[-2400:],flush=True)
    if status:
        print((receipt/'stderr.log').read_text()[-2400:],flush=True)
        sys.exit(status)
