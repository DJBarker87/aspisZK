"""Extract the pinned shipped private leaf from optimized foreign MIR metadata."""
from pathlib import Path
import subprocess,sys,json,hashlib,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin13-20261027'
H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026';S=H+'/gate13/candidate/src';D=H+'/gate13/target-metadata';host='dombarker@100.108.41.90'
phase=sys.argv[1];variant=sys.argv[2] if len(sys.argv)>2 else '';owned=variant.startswith('owned')
if owned:D=H+'/gate13/target-metadata-owned'
assert phase in ['build','charon'];name='pv13-metadata-'+phase+(('-'+sys.argv[2]) if len(sys.argv)>2 else '')
assert not (E/(name+'.json')).exists()
def ssh(c):return subprocess.run(['ssh',host,c],capture_output=True,text=True)
r=ssh(f'python3 {H}/reservation-existing.py {H}/evidence/{name}-reservation.json > {H}/evidence/{name}-reservation.log 2>&1\ncat {H}/evidence/{name}-reservation.log');(E/(name+'-reservation.log')).write_text(r.stdout+r.stderr);ad=json.loads(r.stdout.strip().splitlines()[-1])
if not ad['allowed']:
 (E/(name+'-refusal.json')).write_text(json.dumps(ad,indent=2)+'\n');print('REFUSED',ad);sys.exit(78)
subprocess.run(['scp','-q',f'{host}:{H}/evidence/{name}-reservation.json',str(E)],check=True)
if phase=='build' and owned:
 subprocess.run(['scp','-q',str(R/'tools/pv-runjoin13-20261027/owned-adapter.rs'),f'{host}:{S}/tools/r1-builder-reference/pv_runjoin12_shipped.rs'],check=True)
if phase=='build':cmd=['cargo','build','--manifest-path',S+'/crates/aspis-statement/Cargo.toml','--release','--offline','--locked','--lib','-j','4']
else:
 code='extern crate aspis_statement;\n'
 p=E/'PV_RunJoin_Metadata.rs';p.write_text(code);subprocess.run(['scp','-q',str(p),f'{host}:{H}/evidence/PV_RunJoin_Metadata.rs'],check=True)
 r=ssh('python3 -c '+shlex.quote('from pathlib import Path;print(next(Path('+repr(D+'/release/deps')+').glob("libaspis_statement-*.rlib")))'));assert r.returncode==0,r.stderr;lib=r.stdout.strip()
 cmd=['/home/dombarker/project-offloads/s5-charon-selfid-repair-v1/charon-target/release/charon','rustc','--preset','aeneas','--precise-drops','--desugar-drops','--sysroot','default','--extract-opaque-bodies','--opaque','core','--opaque','alloc','--include','core::option::Option','--include','core::ops::range::Range','--include','aspis_statement::pool_v1::pair_forest_copy_builder::records','--opaque','aspis_statement::pool_v1::pair_trace::pair_empty_roots','--opaque','aspis_statement::pool_v1::pair_forest_copy_builder::raw','--start-from','aspis_statement::pool_v1::pair_forest_copy_builder::records','--dest-file',H+'/evidence/'+name+'.llbc','--',H+'/evidence/PV_RunJoin_Metadata.rs','--crate-name','pv_runjoin_metadata','--crate-type','lib','--edition','2021','--extern','aspis_statement='+lib,'-L','dependency='+D+'/release/deps','--out-dir',H+'/evidence/'+name+'-rustc']
 if len(sys.argv)>2 and sys.argv[2]=='caller':
  cmd[2:2]=['--include','aspis_statement::pool_v1::pair_forest_copy_builder::CopyRecords::new','--start-from','aspis_statement::pool_v1::pair_forest_copy_builder::CopyRecords::new']
 if owned:
  cmd=[a.replace('aspis_statement::pool_v1::pair_forest_copy_builder::records','aspis_statement::pool_v1::pair_forest_copy_builder::records_reference::pv_runjoin12_shipped::records_owned') if a=='aspis_statement::pool_v1::pair_forest_copy_builder::records' else a for a in cmd]
  cmd[2:2]=['--include','aspis_statement::pool_v1::pair_forest_copy_builder::records_reference::pv_runjoin12_shipped::keep_records_owned','--start-from','aspis_statement::pool_v1::pair_forest_copy_builder::records_reference::pv_runjoin12_shipped::keep_records_owned']
 ssh('mkdir -p '+H+'/evidence/'+name+'-rustc')
flags='-Zalways-encode-mir=yes -Zmir-opt-level=4 -Zinline-mir=no -C opt-level=3 -C link-arg=-Wl,--threads=4'
if owned:flags=flags.replace('-Zinline-mir=no','-Zinline-mir=yes -Zinline-mir-threshold=100000 --cfg=aeneas_ref')
if variant=='owned-forwarder':flags+=' -Zinline-mir-forwarder-threshold=100000 -Zinline-mir-hint-threshold=100000'
env=['env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','CARGO_TARGET_DIR='+D,'CARGO_BUILD_JOBS=4','CARGO_PROFILE_RELEASE_OPT_LEVEL=3','RUSTFLAGS='+flags,'PV8_SOURCE_DIR='+S]
record=dict(phase=phase,command=cmd,source_revision='2910da23a3b4a3f780611728d3af122457bbef85',worker_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256((R/'crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs').read_bytes()).hexdigest(),flags=flags,expected_time='optimized native compilation with encoded MIR' if phase=='build' else 'translation of one foreign optimized MIR leaf',axioms='N/A: no Lean compilation',reservation=ad)
(E/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
cmd=['systemd-run','--user','--scope','--quiet','--unit='+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64',*env,'python3',H+'/evidence/pv12-extract-receipt.py',H+'/evidence/'+name,'timeout','240',*cmd]
r=ssh(shlex.join(cmd));(E/(name+'-scope.log')).write_text(r.stdout+r.stderr);print(r.stdout[-3500:]+r.stderr,flush=True)
subprocess.run(['scp','-qr',f'{host}:{H}/evidence/{name}',str(E)],check=True)
p=E/name/'receipt.json';d=json.loads(p.read_text());d.update(expected_time=record['expected_time'],source_revision=record['source_revision'],axioms=record['axioms']);p.write_text(json.dumps(d,indent=2)+'\n')
if phase=='charon':subprocess.run(['scp','-q',f'{host}:{H}/evidence/{name}.llbc',str(E)],check=False)
print((E/name/'out.log').read_text()[-4000:]);sys.exit(r.returncode)
