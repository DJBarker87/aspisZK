"""Single permitted extraction: actual close-account guard scope, frozen source."""
from pathlib import Path
import importlib.util,os,subprocess,json,hashlib,sys
B=Path(__file__).resolve().parent;S=B/'NIK_src';O=B/'NIK_E001_artifacts';O.mkdir(exist_ok=True)
stager=B/'NIK_stage/NHR_stage.py'
spec=importlib.util.spec_from_file_location('NIK_stage',stager);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.validate(S,O,'/home/dombarker/.cargo/bin/cargo')
root=B.parent/'codex-cx-extraction-repro1-20261027/XRa_bin'
pins=dict(frozen_revision=m.REV,stager_sha256=hashlib.sha256(stager.read_bytes()).hexdigest(),lock_before=hashlib.sha256((S/'Cargo.lock').read_bytes()).hexdigest(),root='crate::processor::close_program_account_v1')
for n,h in m.PINS.items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h
pins['tools']=m.PINS
cmd=[str(root/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_statement','--opaque','solana_account_info','--include','core::result::Result','--start-from',pins['root'],'--include',pins['root'],'--dest-file',str(O/'NIK_close.llbc'),'--','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1','--features','r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NIK_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins['charon_command']=cmd
def save(): (O/'NIK_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1))
save()
try:
 r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode;save()
 if not r.returncode:
  pins['llbc_sha256']=hashlib.sha256((O/'NIK_close.llbc').read_bytes()).hexdigest()
  cmd=[str(root/'aeneas-b59d5188-extended'),'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NIK_CloseExtract','-dest',str(O/'raw'),'-subdir','NIK_CloseExtract','-split-files',str(O/'NIK_close.llbc')]
  pins['aeneas_command']=cmd;save();r=subprocess.run(cmd,cwd=B,env=env);pins['aeneas_exit']=r.returncode
finally:
 pins['lock_after']=hashlib.sha256((S/'Cargo.lock').read_bytes()).hexdigest();save();assert pins['lock_after']==pins['lock_before']
sys.exit(r.returncode)
