from pathlib import Path
import json,subprocess,os,hashlib,shutil
E=Path(__file__).resolve().parent;out=E/'NKL_emitted';out.mkdir(exist_ok=False);ref=E/'NKL_ref';(ref/'src').mkdir(parents=True,exist_ok=True)
shutil.copy2(E/'NKL_reference.rs',ref/'src/lib.rs')
(ref/'Cargo.toml').write_text('[package]\nname="nkl_ref"\nversion="0.1.0"\nedition="2021"\n[workspace]\n')
pins={'charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','aeneas-b59d5188-extended':'c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'}
tools=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin')
for n,h in pins.items():assert hashlib.sha256((tools/n).read_bytes()).hexdigest()==h
charon=[str(tools/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--start-from','crate::batch_tree','--dest-file',str(out/'NKL_reference.llbc'),'--','--manifest-path',str(ref/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
aeneas=[str(tools/'aeneas-b59d5188-extended'),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NKL_Reference','-dest',str(out/'raw'),'-subdir','NKL_Reference','-split-files',str(out/'NKL_reference.llbc')]
env={**os.environ,'RUSTUP_TOOLCHAIN':'nightly-2026-09-17','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','RUSTFLAGS':'-Zthreads=1 -Copt-level=3 -C link-arg=-Wl,--threads=1','RAYON_NUM_THREADS':'1'}
x=dict(tools=pins,charon_command=charon,aeneas_command=aeneas,reference_sha256=hashlib.sha256((E/'NKL_reference.rs').read_bytes()).hexdigest(),cargo_target=env['CARGO_TARGET_DIR'])
r=subprocess.run(charon,env=env,cwd=ref);x['charon_exit']=r.returncode
if r.returncode==0:r=subprocess.run(aeneas,env=env,cwd=ref);x['aeneas_exit']=r.returncode
x['outputs']={str(p.relative_to(out)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in out.rglob('*') if p.is_file()}
(out/'NKL_PINS.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(charon=x['charon_exit'],aeneas=x.get('aeneas_exit'))));raise SystemExit(r.returncode)
