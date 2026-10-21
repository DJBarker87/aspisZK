#!/usr/bin/env python3
"""Host-only actual destructor checks. No production source changes."""
import pathlib,subprocess,os,sys,time,json,fcntl,hashlib
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref11-20261021')
S=R/'kani-source'; E=R/'iterator-step'
lock=(R/'rust-stage.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
env=os.environ.copy();env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(R/'kani-target'),ASPIS_SOURCE_REV=sys.argv[1])
name=sys.argv[2]
while True:
    total=0
    for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=p.read_text().strip()
            if v!='max' and (p.parent/'cgroup.procs').read_text().strip():total+=int(v)
        except OSError:pass
    if total+8*2**30<=55*2**30:break
    print('reservation hold',total,flush=True);time.sleep(20)
E.mkdir(exist_ok=True)
(E/(name+'-reservation.json')).write_text(json.dumps(dict(reserved_bytes=total,time=time.time()))+'\n')
(E/(name+'-sources.json')).write_text(json.dumps({str(p.relative_to(S)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for root in ['crates/aspis-core','crates/aspis-statement','tools/r1-builder-reference'] for p in (S/root).rglob('*') if p.is_file() and p.suffix in ['.rs','.toml']},indent=2)+'\n')
cmd=['cargo','kani','-Z','stubbing','-Z','function-contracts','-Z','unstable-options','--manifest-path','tools/r1-builder-reference/Cargo.toml','-j','4','--output-format','terse','--harness',name.split('-')[0],'--cbmc-args','--unwinding-assertions']
if name.startswith('tree_'):
    i=cmd.index('--manifest-path');cmd[i:i+2]=['-p','aspis-statement','--lib']
sys.exit(subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'capped.py'),str(E/name),'Kani compilation then one std iterator/pointer step; no unrolled destructor or arithmetic gate','--','timeout','240',*cmd],cwd=S,env=env).returncode)
