#!/usr/bin/env python3
"""Host-only scoped actual column extraction; retain failed attempts without retries."""
import fcntl, pathlib, subprocess, os, json, hashlib, sys, time
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref7-20261021')
S=R/'source'; E=R/'columns';E.mkdir(exist_ok=True)
lock=(R/'rust-worker.lock').open('w');fcntl.flock(lock,fcntl.LOCK_EX)
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
    rc=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'capped.py'),str(E/name),'Proof compilation then named column wrapper gate '+name,'--','timeout','300',*cmd],cwd=S,env=env|extra).returncode
    print(name,rc,flush=True)
    print((E/name/'stdout.log').read_text()[-4500:],flush=True)
    print((E/name/'stderr.log').read_text()[-2500:],flush=True)
    return rc
mode=sys.argv[2]
if mode=='kani':
    run('kani-limbs',['cargo','kani','-Z','stubbing','-Z','function-contracts','-Z','unstable-options','-p','aspis-statement','--lib','-j','4','--output-format','terse','--harness','nullifier_preimage_contract','--harness','nullifier_preimage_owned_equals_words','--harness','nullifier_callback_owned_equals_shipped','--harness','nullifier_public_owned_equals_shipped','--cbmc-args','--unwinding-assertions'])
else:
    gen=E/'generated';gen.mkdir(exist_ok=True)
    rc=run('charon-columns-fixed',[str(KIT/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built','--start-from','crate::pool_v1::pair_forest_copy_builder::columns','--include','aspis_core::field::*','--dest-file',str(E/'reference.llbc'),'--','--lib','-p','aspis-statement','--release','--offline','-j','4'],dict(RUSTUP_TOOLCHAIN='nightly-2026-06-01',RUSTFLAGS=env['RUSTFLAGS']+' --cfg aeneas_ref',CARGO_TARGET_DIR=str(R/'reference-target')))
    if rc==0:run('aeneas-columns',[str(KIT/'bin/aeneas'),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisBuilderColumnsSource','-dest',str(gen),'-loops-to-rec','-print-unknown-externals',str(E/'reference.llbc')])
