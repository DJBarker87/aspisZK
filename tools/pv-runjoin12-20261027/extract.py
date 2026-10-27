"""One capped extraction, preserving exact inputs and diagnostics."""
import pathlib,subprocess,sys,json,hashlib,shlex
R=pathlib.Path(__file__).resolve().parents[2]; E=R/'evidence/pv-runjoin12-20261027'
H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026'; host='dombarker@100.108.41.90'
name=sys.argv[1];phase=sys.argv[2];assert phase in ['charon','aeneas']
assert not (E/(name+'.json')).exists()
def ssh(s):return subprocess.run(['ssh',host,s],capture_output=True,text=True)
r=ssh(f'python3 {H}/reservation-existing.py {H}/evidence/{name}-reservation.json > {H}/evidence/{name}-reservation.log 2>&1\ncat {H}/evidence/{name}-reservation.log')
(E/(name+'-reservation.log')).write_text(r.stdout+r.stderr)
a=json.loads(r.stdout.strip().splitlines()[-1])
if not a['allowed']:
 (E/(name+'-refusal.json')).write_text(json.dumps(a,indent=2)+'\n');print(a);sys.exit(78)
subprocess.run(['scp','-q',f'{host}:{H}/evidence/{name}-reservation.json',str(E)],check=True)
charon='/home/dombarker/project-offloads/s5-charon-selfid-repair-v1/charon-target/release/charon'
aeneas='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor/candidate-007/main.exe'
llbc=H+'/evidence/PV_RunJoin_Records.llbc'
if phase=='charon':
 cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--include','crate::pool_v1::pair_forest_copy_builder::records','--include','crate::pool_v1::pair_forest_copy_builder::raw','--start-from','crate::pool_v1::pair_forest_copy_builder::records','--dest-file',llbc,'--','--manifest-path',H+'/frozen/crates/aspis-statement/Cargo.toml','--offline','--release','--lib','--jobs','4']
else:
 cmd=[aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PV_RunJoin_Records','-dest',H+'/evidence/'+name+'-generated','-split-files','-emit-json',llbc]
pins=ssh('python3 -c '+shlex.quote('import pathlib,hashlib,json;print(json.dumps({p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest() for p in '+repr([charon,charon+'-driver',aeneas,H+'/frozen/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs'])+'}))'))
record=dict(name=name,phase=phase,command=cmd,tool_source_pins=json.loads(pins.stdout),worker_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),crate_revision='ed1c1cef71-pinned source',opaque_child='pair_empty_roots must resolve to existing extracted implementation; no successful-child assumption',expected_time='optimized compilation then one records MIR translation' if phase=='charon' else 'one records Aeneas translation')
(E/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
subprocess.run(['scp','-q',str(R/'tools/pv-runjoin11-20261027/kani-receipt.py'),f'{host}:{H}/evidence/pv12-extract-receipt.py'],check=True)
env=['env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','CARGO_TARGET_DIR='+H+'/target-charon','CARGO_BUILD_JOBS=4','CARGO_PROFILE_RELEASE_OPT_LEVEL=3','RUSTFLAGS=-C opt-level=3 -C link-arg=-Wl,--threads=4','PV8_SOURCE_DIR='+H+'/frozen']
scope=['systemd-run','--user','--scope','--quiet','--unit='+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64',*env,'python3',H+'/evidence/pv12-extract-receipt.py',H+'/evidence/'+name,'timeout','240',*cmd]
r=ssh(shlex.join(scope));(E/(name+'-scope.log')).write_text(r.stdout+r.stderr);print(r.stdout+r.stderr)
subprocess.run(['scp','-qr',f'{host}:{H}/evidence/{name}',str(E)],check=True)
if phase=='charon':subprocess.run(['scp','-q',f'{host}:{llbc}',str(E)],check=False)
else:subprocess.run(['scp','-qr',f'{host}:{H}/evidence/{name}-generated',str(E)],check=False)
print((E/name/'out.log').read_text()[-14000:])
sys.exit(r.returncode)
