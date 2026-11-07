from pathlib import Path
import hashlib,json,subprocess,os,sys
B=Path(__file__).resolve().parent;S=B/'PCD_src';frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(S/'Cargo.lock')==frozen
assert os.environ['CARGO_NET_OFFLINE']=='true'
cmd=['/home/dombarker/.cargo/bin/cargo','+nightly-2026-09-17','build','--manifest-path',str(S/'crates/aspis-statement/Cargo.toml'),'--offline','--locked','--release','--no-default-features','--features','pool-v1-kernel','--lib','-j','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'PCD_actual_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
(B/'PCD_E005_PHASE.json').write_text(json.dumps(dict(command=cmd,expected_phase='ONLY optimized compilation of the unchanged aspis-statement dependency; no Charon root extraction, no Aeneas, no Kani',lock_before=frozen,toolchain=env['RUSTUP_TOOLCHAIN']),indent=1)+'\n')
try:r=subprocess.run(cmd,cwd=S,env=env)
finally:
 h=sha(S/'Cargo.lock');(B/'PCD_E005-lock-check.json').write_text(json.dumps(dict(before=frozen,after=h,unchanged=h==frozen),indent=1)+'\n');assert h==frozen
sys.exit(r.returncode)
