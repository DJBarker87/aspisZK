"""New extraction021: optimized minimal native test, then exact Charon probe."""
from pathlib import Path
import hashlib,json,os,subprocess
D=Path(__file__).resolve().parent
R=D.parents[2]
manifest=D/'drop-probe/Cargo.toml'
charon=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_TARGET_DIR=str(R.parent/'rng-charon-target'))
cmd=['cargo','test','--manifest-path',str(manifest),'--offline','--release','--jobs','4']
subprocess.run(cmd,cwd=R,env=env,check=True)
cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--precise-drops',
    '--start-from','crate::real_drop','--start-from','crate::counter_probe',
    '--dest-file',str(D/'ProverRwNativeEntropyDropV5.llbc'),'--',
    '--manifest-path',str(manifest),'--offline','--release','--lib','--jobs','4']
pins=dict(command=cmd,charon_sha256=hashlib.sha256(charon.read_bytes()).hexdigest(),
    rustc=subprocess.check_output(['rustc','-Vv'],env=env,text=True),
    source_sha256=hashlib.sha256((D/'drop-probe/lib.rs').read_bytes()).hexdigest(),
    print_axioms='N/A: Rust runtime test and Charon extraction')
(D/'drop-charon-v5-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
raise SystemExit(subprocess.run(cmd,cwd=R,env=env).returncode)
