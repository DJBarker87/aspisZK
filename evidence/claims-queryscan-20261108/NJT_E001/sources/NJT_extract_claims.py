from pathlib import Path
import json,hashlib,subprocess,os,lzma
import NJT_stage as stage
B=Path(__file__).resolve().parent;S=B/'NJT_src';out=B/'NJT_emitted';out.mkdir(exist_ok=True)
n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=S/n;data=p.read_bytes();pins=json.loads((B/'NJT_REFERENCE_PINS.json').read_text());ref=(B/'NJT_claims_ref.rs.txt').read_bytes();original=data[:-(len(ref)+1)]
assert stage.sha(data)==pins['scratch_source'] and stage.sha(original)==pins['frozen_source']
try:
 p.write_bytes(original);stage.validate(S,out,'/home/dombarker/.cargo/bin/cargo')
finally:p.write_bytes(data)
for name,h in stage.PINS.items():assert stage.sha((stage.TOOLROOT/name).read_bytes())==h
llbc=out/'NJT_claims_ref.llbc'
cmd=[str(stage.TOOLROOT/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--start-from','crate::r1_semantic::NJT_claims_ref','--opaque','crate::r1_wire::_::validated_record','--opaque','crate::r1_wire::_::decode_k','--include','aspis_core::field::M31','--include','aspis_core::field::CM31','--include','aspis_core::field::QM31','--dest-file',str(llbc),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1','--features',stage.FEATURES]
aeneas=[str(stage.TOOLROOT/'aeneas-b59d5188-extended'),'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NJT_ClaimsRef','-dest',str(out/'raw'),'-subdir','NJT_ClaimsRef','-split-files',str(llbc)]
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NJT_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
record=dict(charon_command=cmd,aeneas_command=aeneas,tools=stage.PINS,reference=pins,cargo_target_dir=env['CARGO_TARGET_DIR'],lock_before=stage.sha((S/'Cargo.lock').read_bytes()),expected_time='optimized compilation/extraction of owned safe reference only')
try:
 r=subprocess.run(cmd,cwd=S,env=env);record['charon_exit']=r.returncode
 if r.returncode==0:
  doc=json.loads(llbc.read_text());assert not doc['has_errors']
  record['llbc_sha256']=stage.sha(llbc.read_bytes())
  r=subprocess.run(aeneas,cwd=B,env=env);record['aeneas_exit']=r.returncode
 record['exit']=r.returncode
finally:
 record['lock_after']=stage.sha((S/'Cargo.lock').read_bytes());assert record['lock_before']==record['lock_after']
 record['outputs']={str(q.relative_to(out)):stage.sha(q.read_bytes()) for q in (out/'raw').rglob('*') if q.is_file()}
 record['scratch_unchanged']=stage.sha(p.read_bytes())==pins['scratch_source'];assert record['scratch_unchanged']
 if llbc.exists():
  raw=llbc.read_bytes();llbc.with_suffix('.llbc.xz').write_bytes(lzma.compress(raw,preset=6));llbc.with_suffix('.llbc.sha256').write_text(stage.sha(raw)+'\n');llbc.unlink()
 (B/'NJT_EXTRACTION_PINS.json').write_text(json.dumps(record,indent=2)+'\n')
raise SystemExit(r.returncode)
