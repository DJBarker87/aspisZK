from pathlib import Path
import subprocess,os,json,hashlib
b=Path(__file__).resolve().parent;src=b/'NCP_src'
tools={'charon':'/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon','charon-driver':'/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon-driver','aeneas':'/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended'}
pins={k:{'path':v,'sha256':hashlib.sha256(Path(v).read_bytes()).hexdigest(),'bytes':Path(v).stat().st_size} for k,v in tools.items()}
assert pins['charon']['sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert pins['aeneas']['sha256']=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
(b/'NCP_EXTRACTION3_TOOL_PINS.json').write_text(json.dumps(pins,indent=2))
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_TARGET_DIR=str(b/'NCP_extract_target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='--cfg ncp_extract -Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
cmd=[tools['charon'],'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--start-from','crate::NCP_refs::NCP_exact_ref','--start-from','crate::NCP_refs::NCP_canon','--dest-file',str(b/'NCP_helpers.llbc'),'--','--manifest-path',str(src/'crates/aspis-statement/Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1']
print('COMMAND',json.dumps(cmd),flush=True)
r=subprocess.run(cmd,cwd=src,env=env);assert r.returncode==0,r.returncode
out=b/'NCP_helpers_extracted';out.mkdir(exist_ok=True)
cmd=[tools['aeneas'],'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NCP_HelperExtracted','-dest',str(out),'-subdir','NCP_HelperExtracted','-split-files','-emit-json',str(b/'NCP_helpers.llbc')]
print('COMMAND',json.dumps(cmd),flush=True)
r=subprocess.run(cmd,env=env);assert r.returncode==0,r.returncode
files=[b/'NCP_helpers.llbc']+list(out.rglob('*'))
(b/'NCP_EXTRACTION3_OUTPUT_PINS.json').write_text(json.dumps({str(p.relative_to(b)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in files if p.is_file()},indent=2))
