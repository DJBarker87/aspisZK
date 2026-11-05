"""Owned Pool leaf extraction after exact NHR_stage.py staging/checking."""
from pathlib import Path
import subprocess,json,hashlib,sys,os,importlib.util
B=Path(__file__).resolve().parent;cfg=json.loads((B/sys.argv[1]).read_text());a=cfg['attempt'];S=B/'NIE_src';O=B/(a+'_extracted');O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
stager=B/'NIE_stage/NHR_stage.py'
assert sha(stager)==cfg['stager_sha256']
# Restore the actual frozen callers before the stager checks the whole corpus.
previous=B/'NIE_applied.patch';patch=previous.read_bytes() if previous.exists() else None
pins=dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',stager_sha256=sha(stager),leaf=cfg['leaf_selector'],namespace=cfg['extract_namespace'],lock_before=sha(S/'Cargo.lock'))
status=1
def save(phase):
 pins['phase']=phase;(B/(a+'_EXTRACTION_PINS.json')).write_text(json.dumps(pins,indent=2)+'\n')
save('before staging')
try:
 if patch and 'mod NIE_native {' in (S/'programs/aspis-pool/src/pair_forest.rs').read_text():subprocess.run(['git','apply','--reverse',str(previous)],cwd=S,check=True)
 check=['python3',str(stager),'--check','--workspace',str(S),'--out',str(O/'staging')]
 pins['staging_command']=check;save('NHR staging/metadata');r=subprocess.run(check,cwd=B);pins['staging_exit']=r.returncode
 assert r.returncode==0,'NHR frozen staging check failed'
 spec=importlib.util.spec_from_file_location('NIE_stager',stager);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 module.validate(S,O/'staging','/home/dombarker/.cargo/bin/cargo')
 # Same stricter frozen/deployed native gate, now with the restored source map.
 manifest=json.loads((B/'NIE_RUST_SHA256.json').read_text())
 for n in list(manifest):
  if (S/n).is_file():manifest[n]=sha(S/n)
 (B/'NIE_RUST_SHA256.json').write_text(json.dumps(manifest))
 save('Pool deployed graph validation')
 r=subprocess.run(['python3','NIE_kani_gate.py',sys.argv[1]],cwd=B);pins['pool_graph_exit']=r.returncode
 assert r.returncode==0,'Pool frozen graph preflight failed'
 root=B.parent/'codex-cx-extraction-repro1-20261027/XRa_bin';charon=root/'charon';aeneas=root/'aeneas-b59d5188-extended'
 assert sha(charon)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
 assert sha(aeneas)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
 cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_statement','--opaque','solana_account_info','--include','core::result::Result','--start-from','crate::'+cfg['leaf_selector'],'--include','crate::'+cfg['leaf_selector'],'--dest-file',str(B/(a+'.llbc')),'--','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1','--features',cfg['program_features']]
 env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NIE_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
 pins['charon_command']=cmd;pins['tool_sha256']={str(charon):sha(charon),str(aeneas):sha(aeneas)}
 save('optimized compilation / Charon target '+cfg['leaf_selector'])
 r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode;status=r.returncode
 if not status:
  pins['llbc_sha256']=sha(B/(a+'.llbc'))
  cmd=[str(aeneas),'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',cfg['extract_namespace'],'-dest',str(O/'raw'),'-subdir',cfg['extract_namespace'],'-split-files',str(B/(a+'.llbc'))]
  pins['aeneas_command']=cmd;save('Aeneas selected body');r=subprocess.run(cmd,cwd=B,env=env);pins['aeneas_exit']=r.returncode;status=r.returncode
finally:
 pins['lock_after']=sha(S/'Cargo.lock');pins['outputs']={str(p.relative_to(B)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in O.rglob('*') if p.is_file()}
 pins['exit']=status;(B/(a+'_EXTRACTION_PINS.json')).write_text(json.dumps(pins,indent=2)+'\n')
 if patch:subprocess.run(['git','apply',str(previous)],cwd=S,check=True)
 assert pins['lock_after']==pins['lock_before']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
sys.exit(status)
