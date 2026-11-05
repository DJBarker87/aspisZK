"""Single permitted extraction: actual uniqueness helper, explicit outer carrier type."""
from pathlib import Path
import importlib.util,os,subprocess,json,hashlib,sys
B=Path(__file__).resolve().parent;S=B/'NIO_src';O=B/'NIO_E001_artifacts';O.mkdir(exist_ok=True)
stager=B/'NIO_stage/NHR_stage.py'
spec=importlib.util.spec_from_file_location('NIO_stage',stager);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
# Restore ONLY our own staged corpus to the manifest before NHR validation.
import base64,lzma
manifest=json.loads((B/'NIO_stage/NHR_STAGING_MANIFEST.json').read_text())
raw=lzma.decompress((B/'NIO_stage/NHR_FROZEN_PAYLOAD.json.xz').read_bytes())
assert hashlib.sha256(raw).hexdigest()==(B/'NIO_stage/NHR_FROZEN_PAYLOAD.json.sha256').read_text().strip()
for name,encoded in json.loads(raw).items():
 data=base64.b64decode(encoded);assert hashlib.sha256(data).hexdigest()==manifest['files'][name]['sha256'];(S/name).write_bytes(data)
(B/'NIO_applied.patch').unlink(missing_ok=True)
m.validate(S,O,'/home/dombarker/.cargo/bin/cargo')
root=B.parent/'codex-cx-extraction-repro1-20261027/XRa_bin'
pins=dict(frozen_revision=m.REV,stager_sha256=hashlib.sha256(stager.read_bytes()).hexdigest(),lock_before=hashlib.sha256((S/'Cargo.lock').read_bytes()).hexdigest(),root='crate::processor::require_unique_accounts')
for n,h in m.PINS.items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h
pins['tools']=m.PINS
cmd=[str(root/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_statement','--opaque','solana_account_info','--include','solana_account_info::AccountInfo','--include','solana_pubkey::Pubkey','--include','solana_program_error::ProgramError','--include','core::result::Result','--start-from',pins['root'],'--include',pins['root'],'--dest-file',str(O/'NIO_unique.llbc'),'--','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1','--features','r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NIO_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins['charon_command']=cmd
def save(): (O/'NIO_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1))
save()
try:
 r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode;save()
 if not r.returncode:
  pins['llbc_sha256']=hashlib.sha256((O/'NIO_unique.llbc').read_bytes()).hexdigest()
  cmd=[str(root/'aeneas-b59d5188-extended'),'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NIO_UniqueExtract','-dest',str(O/'raw'),'-subdir','NIO_UniqueExtract','-split-files',str(O/'NIO_unique.llbc')]
  pins['aeneas_command']=cmd;save();r=subprocess.run(cmd,cwd=B,env=env);pins['aeneas_exit']=r.returncode
finally:
 pins['mitigation_files_retained']={n:hashlib.sha256((S/n).read_bytes()).hexdigest() for n in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']}
 pins['lock_after']=hashlib.sha256((S/'Cargo.lock').read_bytes()).hexdigest();save();assert pins['lock_after']==pins['lock_before']
sys.exit(r.returncode)
