"""Frozen Pool leaves, with named opaque callees, using the NCO tool pins."""
from pathlib import Path
import subprocess,json,hashlib,os,sys
B=Path(__file__).resolve().parent;cfg=json.loads((B/sys.argv[1]).read_text());a=cfg['attempt'];S=B/'NHC_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
C=B.parent/'codex-cx-extraction-repro1-20261027/XRa_bin/charon';A=C.parent/'aeneas-b59d5188-extended'
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
# The identical strict frozen/deployed graph check also records every feature.
r=subprocess.run(['python3','NHC_kani_gate.py',sys.argv[1]],cwd=B);assert r.returncode==0
leaves=cfg['leaf_selectors'];ns=cfg['extract_namespace'];D=B/(a+'_extracted');D.mkdir(exist_ok=True)
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_statement','--include','core::result::Result']
for n in leaves:cmd+=['--start-from','crate::'+n,'--include','crate::'+n]
if a=='NHC_E002':cmd+=['--include','crate::pair_forest::PoolV1PairForestTerminalBumpHintsV1']
cmd+=['--dest-file',str(B/(a+'.llbc')),'--','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'--offline','--release','--lib','--jobs','1','--features',cfg['program_features']]
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NHC_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,namespace=ns,source_lock_before=sha(S/'Cargo.lock'),leaf_selectors=leaves,opaque_children=['crate except listed leaves','aspis_statement'],toolchain='nightly-2026-09-17')
(B/(a+'_EXTRACTION_PINS.json')).write_text(json.dumps(pins,indent=1)+'\n')
r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode
if not r.returncode:
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',str(D),'-subdir',ns,'-split-files',str(B/(a+'.llbc'))]
 pins['aeneas_command']=cmd;r=subprocess.run(cmd,cwd=B,env=env);pins['aeneas_exit']=r.returncode
pins['outputs']={str(p.relative_to(B)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in D.rglob('*') if p.is_file()}
pins['source_lock_after']=sha(S/'Cargo.lock');assert pins['source_lock_before']==pins['source_lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
(B/(a+'_EXTRACTION_PINS.json')).write_text(json.dumps(pins,indent=1)+'\n');sys.exit(r.returncode)
