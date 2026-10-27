"""Read deterministic source fixture words with a capped optimized native probe."""
import pathlib,subprocess,sys,json,shlex,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027';host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026'
name=sys.argv[1];phase=sys.argv[2];assert phase in ['build','charon'];assert not (E/(name+'.json')).exists()
def ssh(s):return subprocess.run(['ssh',host,s],capture_output=True,text=True)
r=ssh(f'python3 {H}/reservation-existing.py {H}/evidence/{name}-reservation.json > {H}/evidence/{name}-reservation.log 2>&1\ncat {H}/evidence/{name}-reservation.log');(E/(name+'-reservation.log')).write_text(r.stdout+r.stderr);a=json.loads(r.stdout.strip().splitlines()[-1])
if not a['allowed']:
 (E/(name+'-refusal.json')).write_text(json.dumps(a,indent=2)+'\n');print(a);sys.exit(78)
subprocess.run(['scp','-q',f'{host}:{H}/evidence/{name}-reservation.json',str(E)],check=True)
prefix='tools/pv-runjoin12-20261027'
r=ssh('mkdir -p '+H+'/frozen/'+prefix);assert r.returncode==0
paths=[prefix+'/foreign-root.rs']
for p in paths:subprocess.run(['scp','-q',str(R/p),f'{host}:{H}/frozen/{p}'],check=True)
subprocess.run(['scp','-q',str(R/'tools/pv-runjoin12-20261027/kani-receipt.py'),f'{host}:{H}/evidence/pv12-native-receipt.py'],check=True)
if phase=='build':
 cmd=['cargo','build','--release','--offline','--manifest-path',H+'/frozen/crates/aspis-statement/Cargo.toml','--lib','--jobs','4','--message-format=json']
else:
 artifact=json.loads((E/'foreign-mir-artifact.json').read_text())['rlib']
 charon='/home/dombarker/project-offloads/s5-charon-selfid-repair-v1/charon-target/release/charon'
 cmd=[charon,'rustc','--preset','aeneas','--extract-opaque-bodies','--include','aspis_statement','--opaque','core','--include','core::ops::function','--include','core::option::Option','--include','core::ops::control_flow::ControlFlow','--opaque','aspis_statement::pool_v1::pair_forest_copy_builder::raw','--mir','optimized','--sysroot','default','--precise-drops','--desugar-drops','--opaque','aspis_statement::pool_v1::pair_trace::pair_empty_roots','--include','aspis_core::field::*','--start-from','aspis_statement::pool_v1::pair_forest_copy_builder::records_reference::pv_runjoin12_shipped::records_owned','--dest-file',H+'/evidence/'+name+'.llbc','--','--crate-name','pv_runjoin12_foreign','--crate-type','lib','--edition=2021',H+'/frozen/'+prefix+'/foreign-root.rs','--extern','aspis_statement='+artifact,'-L','dependency='+str(pathlib.PurePosixPath(artifact).parent/'deps')]
pin_paths=['/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc']+([charon,charon+'-driver',artifact] if phase=='charon' else [])
pinned=ssh('python3 -c '+shlex.quote('import pathlib,hashlib,json;print(json.dumps({p:dict(sha256=hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest(),size=pathlib.Path(p).stat().st_size) for p in '+repr(pin_paths)+'}))'))
assert pinned.returncode==0,pinned.stderr
record=dict(tool_and_mir_pins=json.loads(pinned.stdout),compiler_env=dict(RUSTUP_TOOLCHAIN='nightly-2026-06-01',RUSTFLAGS='-C opt-level=3 -Z mir-opt-level=4 -Z inline-mir=yes -Z inline-mir-threshold=100000 -Z inline-mir-forwarder-threshold=100000 -Z inline-mir-hint-threshold=100000 -Z always-encode-mir --cfg aeneas_ref -C link-arg=-Wl,--threads=4'),target=cmd,worker_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_revision='ed1c1cef71-pinned records leaf; cfg owned borrow adapter, normal rustc MIR4',expected_time='optimized dependency compilation with all MIR retained, then foreign-root translation; no verification',source_sha256={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths})
(E/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
scope=['systemd-run','--user','--scope','--quiet','--unit='+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+H+'/target-charon','CARGO_BUILD_JOBS=4','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=-C opt-level=3 -Z mir-opt-level=4 -Z inline-mir=yes -Z inline-mir-threshold=100000 -Z inline-mir-forwarder-threshold=100000 -Z inline-mir-hint-threshold=100000 -Z always-encode-mir --cfg aeneas_ref -C link-arg=-Wl,--threads=4','PV8_SOURCE_DIR='+H+'/frozen','python3',H+'/evidence/pv12-native-receipt.py',H+'/evidence/'+name,'timeout','240',*cmd]
r=ssh(shlex.join(scope));(E/(name+'-scope.log')).write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',f'{host}:{H}/evidence/{name}',str(E)],check=True)
p=E/name/'receipt.json';d=json.loads(p.read_text());d['executed_target']=d['target'];d.update(record);d['axioms']='N/A: MIR preparation/translation; not a Lean theorem';d['classification']='normal optimized MIR input for unchanged pinned Charon; no source association accepted yet';p.write_text(json.dumps(d,indent=2)+'\n')
if phase=='build' and r.returncode==0:
 artifacts=[]
 for line in (E/name/'out.log').read_text().splitlines():
  try:x=json.loads(line)
  except json.JSONDecodeError:continue
  if x.get('reason')=='compiler-artifact' and x.get('target',{}).get('name')=='aspis_statement':
   artifacts.extend(f for f in x['filenames'] if f.endswith('.rlib'))
 assert len(artifacts)==1,artifacts
 (E/'foreign-mir-artifact.json').write_text(json.dumps(dict(rlib=artifacts[0],build_receipt=name+'/receipt.json',rustflags='opt3,mir4,inline-mir,threshold100000,always-encode-mir,cfg(aeneas_ref)',classification='binary remains only in retained own host cache'),indent=2)+'\n')
if phase=='charon':subprocess.run(['scp','-q',f'{host}:{H}/evidence/{name}.llbc',str(E/(name+'.llbc'))],check=False)
print('foreign MIR phase collected',name,phase);sys.exit(r.returncode)
