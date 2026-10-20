#!/usr/bin/env python3
"""Run actual unmodified prover salt cone once, stopping on translation failure."""
import argparse, hashlib, json, os, subprocess
from pathlib import Path
R=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020')
CHARON='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
AENEAS='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
os.chdir(R/'src')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'], CARGO_TARGET_DIR=str(R/'charon-target'), CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
def pin(p):
    p=Path(p); return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def reservation(memory_gib):
    populated=[]
    for p in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=p.read_text().strip()
            if v!='max' and (p.parent/'cgroup.procs').read_text().strip(): populated.append({'path':str(p.parent),'bytes':int(v)})
        except (OSError,PermissionError): pass
    if sum(x['bytes'] for x in populated)+memory_gib*2**30 >55*2**30:
        (R/'reservation-hold.json').write_text(json.dumps(populated,indent=2)+'\n')
        raise SystemExit(f'RESERVATION HOLD: current populated caps plus {memory_gib} GiB exceed 55 GiB')
    return populated
pins={'source_revision':'f2a598c6a','tools':[pin(CHARON),pin(AENEAS)],'sources':[pin(R/'src'/p) for p in ['crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-prover/src/state_only_entropy.rs','crates/aspis-prover/src/state_only_hiding.rs','crates/aspis-core/src/state_only_hiding.rs','crates/aspis-core/src/state_only_private_merkle.rs','Cargo.lock']]}
(R/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
def run(label,cmd,memory_gib=2):
    (R/(label+'-source-pins.json')).write_text(json.dumps(pins,indent=2)+'\n'); gate=reservation(memory_gib); (R/(label+'-reservation.json')).write_text(json.dumps(gate,indent=2)+'\n')
    return subprocess.run(['systemd-run','--user','--scope','-p',f'MemoryHigh={1800 if memory_gib==2 else (memory_gib-2)*1024}M','-p',f'MemoryMax={memory_gib}G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'harness/capped.py'),str(R/'receipts'/label),'Optimized compilation and pinned translation only; no arithmetic execution or proof generation','--',*cmd]).returncode
cmd=[CHARON,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err','--start-from','crate::state_only_entropy::_::next_word','--start-from','crate::state_only_entropy::_::m31','--start-from','crate::state_only_hiding::_::next_word','--start-from','crate::state_only_hiding::_::m31','--start-from','crate::state_only_hiding::derive_state_only_mask_seed_from_entropy_ref','--include','aspis_core::state_only_hiding','--opaque','aspis_core','--dest-file',str(R/'extraction/StreamsCommit.llbc'),'--','--manifest-path',str(R/'src/crates/aspis-prover/Cargo.toml'),'--locked','--offline','--release','--lib','--no-default-features','--features','r0','--jobs','4']
ap=argparse.ArgumentParser(); ap.add_argument('--resume-aeneas',action='store_true'); args=ap.parse_args()
if not args.resume_aeneas:
    status=run('streams-charon',cmd)
    if status: raise SystemExit(status)
(R/'llbc-pin.json').write_text(json.dumps(pin(R/'extraction/StreamsCommit.llbc'),indent=2)+'\n')
raise SystemExit(run('streams-aeneas',[AENEAS,'-log-debug','Translate,InterpLoops','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1ProverStreams','-dest',str(R/'extraction/generated-streams'),'-subdir','AspisR1ProverStreams','-split-files','-emit-json',str(R/'extraction/StreamsCommit.llbc')],memory_gib=2))
