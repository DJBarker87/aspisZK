#!/usr/bin/env python3
"""Focused optimized MIR extraction and translation, in a capped NUC scope.
Time is expected in dependency-free Rust compilation and MIR/Lean translation,
not in finite-field elimination or witness generation.
"""
import argparse, hashlib, json, os, shutil, subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
root=Path('/home/dombarker/project-offloads');kit=Path(__file__).parent/'r64-field-extraction'
stage=root/'aspis-r20-r62-gather-20260929-b'
charon=root/'ZK-v5-formal/toolchains/charon/bin/charon'
aeneas=root/'aspis-v7-aeneas-source-unblock-20260830/aeneas-repro-r1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(charon)=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
assert sha(aeneas)=='e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813'
manifest=json.loads((stage/'r18-stage.json').read_text())
for n,h in manifest['files'].items():assert sha(stage/n)==h,n
assert not a.output.exists();a.output.mkdir();source=a.output/'source';source.mkdir()
for n in ['Cargo.toml','lib.rs']:shutil.copy2(kit/n,source/n)
for n in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']:
    path='crates/aspis-core/src/'+n;assert path in manifest['files'];shutil.copy2(stage/path,source/n)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',
    CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=str(a.output/'target'),NO_DNA='1')
(a.output/'environment.json').write_text(json.dumps({k:env[k] for k in [
    'RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','CARGO_TARGET_DIR']},indent=2)+'\n')
records=[]
def run(label,cmd):
    with (a.output/(label+'.log')).open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*map(str,cmd)],cwd=source,env=env,stdout=f,stderr=subprocess.STDOUT)
    records.append({'label':label,'command':list(map(str,cmd)),'exit':r.returncode})
    (a.output/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
    print((a.output/(label+'.log')).read_text(),flush=True)
    if r.returncode:raise SystemExit(r.returncode)
run('lock',['cargo','generate-lockfile','--offline'])
run('extract',[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::inverse_probe',
    '--dest-file',a.output/'R64Field.llbc','--','--locked','--offline','--release','--lib','--no-default-features'])
run('translate',[aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR64Field',
    '-dest',a.output/'generated','-subdir','AspisR64Field','-split-files','-emit-json',a.output/'R64Field.llbc'])
pins={str(p.relative_to(a.output)):sha(p) for folder in [source,a.output/'generated'] for p in folder.rglob('*') if p.is_file()}
pins['R64Field.llbc']=sha(a.output/'R64Field.llbc')
(a.output/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
print(json.dumps({'status':'PASS','pinned_files':len(pins)}))
