from pathlib import Path
import subprocess,os,json,hashlib
E=Path(__file__).resolve().parent
r=subprocess.run(['python3','NHR_stage.py','--check','--out','NJI_WARM_PREFLIGHT'],capture_output=True,text=True)
assert r.returncode==0,r.stderr
w=E/'NHR_workspace';before=hashlib.sha256((w/'Cargo.lock').read_bytes()).hexdigest()
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(E/'NJI_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
cmd=['/home/dombarker/.cargo/bin/cargo','build','--manifest-path',str(w/'Cargo.toml'),'--locked','--offline','--release','-p','aspis-statement','--features','r0,pool-v1-kernel','--lib','--jobs','1']
r=subprocess.run(cmd,env=env,capture_output=True,text=True)
(E/'NJI_WARM.stdout').write_text(r.stdout);(E/'NJI_WARM.stderr').write_text(r.stderr)
after=hashlib.sha256((w/'Cargo.lock').read_bytes()).hexdigest();assert before==after
files=list((E/'NJI_target/release/deps').glob('*.rlib'))
(E/'NJI_WARM.json').write_text(json.dumps(dict(command=cmd,exit=r.returncode,lock_before=before,lock_after=after,objects=len(files),bytes=sum(p.stat().st_size for p in files),expected_time='optimized compilation of unchanged statement dependency closure, no proof generation or elimination')))
print(json.dumps(dict(exit=r.returncode,objects=len(files))));raise SystemExit(r.returncode)
