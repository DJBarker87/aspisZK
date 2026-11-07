from pathlib import Path
import subprocess,json,hashlib,os
B=Path.cwd();S=B/'PCI_single_crate';C=B.parent/'codex-cx-extraction-repro1-20261027/XRa_bin/charon';A=C.parent/'aeneas-b59d5188-extended'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
lock=sha(B/'PCI_src/Cargo.lock');assert lock=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default']
for root in ['single_reference']:cmd+=['--start-from','crate::'+root]
cmd+=['--dest-file',str(B/'PCI_single.llbc'),'--','--manifest-path',str(S/'Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'PCI_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1 --cfg PCI_EXTRACT',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,lock_before=lock,reference_source=sha(S/'src/lib.rs'),reference_manifest=sha(S/'Cargo.toml'),reference_lock=sha(S/'Cargo.lock'),reference_single='Value-only single-output reference; all raw commitment words, full owned zero witness on success and exact NonCanonicalCommitment error tag.',toolchain='nightly-2026-09-17')
(B/'PCI_SINGLE_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1));r=subprocess.run(cmd,cwd=S,env=env)
if not r.returncode:
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PCI_SingleRef','-dest',str(B/'PCI_single_extracted'),'-subdir','PCI_SingleRef','-split-files',str(B/'PCI_single.llbc')];pins['aeneas_command']=cmd;r=subprocess.run(cmd,cwd=B,env=env)
pins.update(exit=r.returncode,lock_after=sha(B/'PCI_src/Cargo.lock'),outputs={str(p.relative_to(B)):sha(p) for p in (B/'PCI_single_extracted').rglob('*') if p.is_file()})
(B/'PCI_SINGLE_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1));assert pins['lock_after']==lock
raise SystemExit(r.returncode)
