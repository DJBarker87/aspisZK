#!/usr/bin/env python3
"""Host-only scoped nullifier P6 gates; retain failed attempts without retries."""
import fcntl, pathlib, subprocess, os, json, hashlib, sys, time
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref8-20261021')
S=R/'carry-source'; E=R/'carry';E.mkdir(exist_ok=True)
lock=(R/'carry-worker.lock').open('w');fcntl.flock(lock,fcntl.LOCK_EX)
KIT=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
env=os.environ.copy();env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4',ASPIS_SOURCE_REV=sys.argv[1])
def run(name,cmd,extra={}):
    assert not (E/name/'receipt.json').exists()
    while True:
        total=0
        for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
            try:
                v=p.read_text().strip()
                if v!='max' and (p.parent/'cgroup.procs').read_text().strip():total+=int(v)
            except OSError:pass
        if total+8*2**30<=55*2**30:break
        print('reservation hold',total,flush=True);time.sleep(20)
    (E/(name+'-reservation.json')).write_text(json.dumps(dict(reserved_before_bytes=total,limit_bytes=55*2**30,job_max_bytes=8*2**30,time=time.time()))+'\n')
    rc=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'capped.py'),str(E/name),'Proof compilation then named owned-tree gate '+name,'--','timeout','240',*cmd],cwd=S,env=env|extra).returncode
    print(name,rc,flush=True)
    print((E/name/'stdout.log').read_text()[-4500:],flush=True)
    print((E/name/'stderr.log').read_text()[-2500:],flush=True)
    return rc
mode=sys.argv[2]
if mode=='literal':
    run('kani-literal',['cargo','kani','-Z','stubbing','-Z','unstable-options','-p','aspis-statement','--lib','-j','4','--output-format','terse','--harness','owned_tree_literal_one','--cbmc-args','--unwinding-assertions'])
else:
    gen=E/'generated';gen.mkdir(exist_ok=True)
    rc=run('charon-entry',[str(KIT/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built','--start-from','crate::pool_v1::incremental_merkle::tree_reference::carry_owned_with','--include','aspis_core::field::*','--dest-file',str(E/'reference-entry.llbc'),'--','--lib','-p','aspis-statement','--release','--offline','-j','4'],dict(RUSTUP_TOOLCHAIN='nightly-2026-06-01',RUSTFLAGS=env['RUSTFLAGS']+' --cfg aeneas_ref',CARGO_TARGET_DIR=str(R/'carry-target')))
    if rc==0:run('aeneas-entry',[str(KIT/'bin/aeneas'),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisBuilderTreeReference','-dest',str(gen),'-loops-to-rec','-print-unknown-externals',str(E/'reference-entry.llbc')])
