from pathlib import Path
import subprocess,hashlib,json,os
b=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tools=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin')
charon=tools/'charon';aeneas=tools/'aeneas-b59d5188-extended'
assert sha(charon)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(aeneas)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
assert not (b/'NJH_EXTRACTION_LAUNCHED.json').exists()
roots=['shared_ref','exclusive_ref','shared_drop_ref','exclusive_drop_ref','copy_window_ref','clock_ref','pda_reply_ref']
cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result']
for root in roots:cmd+=['--start-from','crate::'+root]
cmd+=['--dest-file',str(b/'NJH_reference.llbc'),'--','--manifest-path',str(b/'NJH_ref/Cargo.toml'),'--offline','--release','--lib','--jobs','1']
env={**os.environ,'RUSTUP_TOOLCHAIN':'nightly-2026-09-17','RUSTFLAGS':'-Zthreads=1 -C link-arg=-Wl,--threads=1'}
pins=dict(charon_sha256=sha(charon),aeneas_sha256=sha(aeneas),rust_reference_sha256=sha(b/'NJH_ref/src/lib.rs'),charon_command=cmd,roots=roots,CARGO_TARGET_DIR=os.environ['CARGO_TARGET_DIR'])
(b/'NJH_EXTRACTION_LAUNCHED.json').write_text(json.dumps(pins,indent=1))
r=subprocess.run(cmd,env=env);pins['charon_exit']=r.returncode
if r.returncode==0:
 cmd2=[str(aeneas),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NJH_Ref','-dest',str(b/'NJH_extracted'),'-subdir','NJH_Ref','-split-files',str(b/'NJH_reference.llbc')]
 pins['aeneas_command']=cmd2;r=subprocess.run(cmd2,env=env);pins['aeneas_exit']=r.returncode
pins['outputs']={str(p.relative_to(b)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in (b/'NJH_extracted').rglob('*') if p.is_file()}
(b/'NJH_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1))
raise SystemExit(r.returncode)
