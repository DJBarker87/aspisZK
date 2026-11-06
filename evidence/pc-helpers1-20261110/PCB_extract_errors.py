from pathlib import Path
import subprocess,json,hashlib,os
B=Path.cwd();S=B/'PCB_src/crates/aspis-statement';C=B.parent/'codex-cx-extraction-repro1-20261027/XRa_bin/charon';A=C.parent/'aeneas-b59d5188-extended'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
lock=sha(B/'PCB_src/Cargo.lock');assert lock=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default']
for stem,id in [('authorization_receipt','159'),('authorization_receipt_account','160'),('pair_forest_accounts','189')]:cmd+=['--start-from',f'crate::pool_v1::{stem}::PCB_{id}::reference']
cmd+=['--dest-file',str(B/'PCB_errors.llbc'),'--','--manifest-path',str(S/'Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1','--features','pool-v1-kernel']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'PCB_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1 --cfg PCB_EXTRACT',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,lock_before=lock,reference_sources={str(p.relative_to(B)):sha(p) for p in (S/'src/pool_v1').glob('PCB_*.rs')},toolchain='nightly-2026-09-17')
(B/'PCB_ERROR_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1));r=subprocess.run(cmd,cwd=S,env=env)
if not r.returncode:
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PCB_ErrorRef','-dest',str(B/'PCB_errors_extracted'),'-subdir','PCB_ErrorRef','-split-files',str(B/'PCB_errors.llbc')];pins['aeneas_command']=cmd;r=subprocess.run(cmd,cwd=B,env=env)
pins.update(exit=r.returncode,lock_after=sha(B/'PCB_src/Cargo.lock'),outputs={str(p.relative_to(B)):sha(p) for p in (B/'PCB_errors_extracted').rglob('*') if p.is_file()})
(B/'PCB_ERROR_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1));assert pins['lock_after']==lock
raise SystemExit(r.returncode)
