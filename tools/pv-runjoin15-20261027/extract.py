"""One capped extraction, preserving exact inputs and diagnostics."""
import pathlib,subprocess,sys,json,hashlib,shlex
R=pathlib.Path(__file__).resolve().parents[2]; E=R/'evidence/pv-runjoin15-20261027'
H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026'; host='dombarker@100.108.41.90'
name=sys.argv[1];phase=sys.argv[2];assert phase in ['charon','aeneas']
if phase=='aeneas' and len(sys.argv)>3:
 preflight=E/(sys.argv[3]+'.llbc')
 if preflight.exists():
  data=json.loads(preflight.read_text());assert not data['has_errors'], 'reject LLBC with translation errors'
  assert isinstance(data['translated']['fun_decls'][0]['body'],dict), 'reject opaque root before extraction: no implementation body'

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
llbc=H+'/evidence/'+(name if phase=='charon' else (sys.argv[3] if len(sys.argv)>3 else 'PV_RunJoin_Records'))+'.llbc'
if phase=='aeneas' and (E/(pathlib.Path(llbc).name)).is_file():
 subprocess.run(['scp','-q',str(E/pathlib.Path(llbc).name),f'{host}:{llbc}'],check=True)
if phase=='charon' and len(sys.argv)>3 and sys.argv[3] in ['shipped-owned','shipped-owned-force']:
 for p in ['tools/r1-builder-reference/records_reference.rs','tools/r1-builder-reference/pv_runjoin12_shipped.rs']:
  subprocess.run(['scp','-q',str(R/p),f'{host}:{H}/gate13/candidate/src/{p}'],check=True)
if phase=='charon':
 cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--include','crate::pool_v1::pair_forest_copy_builder::records','--include','crate::pool_v1::pair_forest_copy_builder::raw','--start-from','crate::pool_v1::pair_forest_copy_builder::records','--dest-file',llbc,'--','--manifest-path',H+'/gate13/candidate/src/crates/aspis-statement/Cargo.toml','--offline','--release','--lib','--jobs','4']
 if len(sys.argv)>3 and sys.argv[3] in ['optimized','precise','precise-all','precise-poly','precise-real','shipped-owned','shipped-owned-force']:
  cmd[cmd.index('built')]='optimized'
  start=cmd.index('--opaque');end=cmd.index('--start-from');cmd[start:end]=['--opaque','crate::pool_v1::pair_trace::pair_empty_roots','--include','aspis_core::field::*']
  if sys.argv[3].startswith('precise') or sys.argv[3] in ['shipped-owned','shipped-owned-force']:
   cmd[2:2]=['--precise-drops','--desugar-drops']
   if sys.argv[3] not in ['precise-poly','precise-real','shipped-owned','shipped-owned-force']:cmd[2:2]=['--monomorphize']
   if sys.argv[3]=='precise-all':cmd[2:2]=['--translate-all-methods']
   if sys.argv[3] in ['precise-real','shipped-owned','shipped-owned-force']:cmd[2:2]=['--rustc-arg=-Zmir-enable-passes=+Inline,+GVN,+CopyProp','--rustc-arg=-Zinline-mir=yes']
 if len(sys.argv)>3 and sys.argv[3]=='shipped-owned-force':
  cmd.remove('--rustc-arg=-Zmir-enable-passes=+Inline,+GVN,+CopyProp')
  cmd[2:2]=['--opaque','crate::pool_v1::pair_forest_copy_builder::raw','--duplicate-defaulted-methods','--rustc-arg=-Zmir-enable-passes=+Inline,+GVN,+CopyProp,+DataflowConstProp,+SimplifyLocals-final,+SimplifyCfg-final']
 if len(sys.argv)>3 and sys.argv[3] in ['shipped-owned','shipped-owned-force']:
  cmd[cmd.index('crate::pool_v1::pair_forest_copy_builder::records')]='crate::pool_v1::pair_forest_copy_builder::records_reference::pv_runjoin12_shipped::records_owned'
  cmd[2:2]=['--rustc-arg=--cfg=aeneas_ref','--rustc-arg=-Zinline-mir-threshold='+('100000' if sys.argv[3]=='shipped-owned-force' else '1000')]
 if len(sys.argv)>4:
  old='crate::pool_v1::pair_forest_copy_builder::records_reference::pv_runjoin12_shipped::records_owned'
  cmd[cmd.index(old)]=old.removesuffix('records_owned')+sys.argv[4]
 if len(sys.argv)>3 and sys.argv[3] in ['precise-real-raw-opaque','mono-raw-opaque']:
  cmd[cmd.index('built')]='optimized'
  start=cmd.index('--opaque');end=cmd.index('--start-from');cmd[start:end]=['--opaque','crate::pool_v1::pair_trace::pair_empty_roots','--opaque','crate::pool_v1::pair_forest_copy_builder::raw','--include','aspis_core::field::*']
  cmd[2:2]=['--precise-drops','--desugar-drops','--duplicate-defaulted-methods','--rustc-arg=-Zmir-enable-passes=+Inline,+GVN,+CopyProp,+DataflowConstProp,+SimplifyLocals-final,+SimplifyCfg-final','--rustc-arg=-Zinline-mir=yes']
 if len(sys.argv)>3 and sys.argv[3]=='mono-raw-opaque':cmd[2:2]=['--monomorphize']
else:
 cmd=[aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PV_RunJoin_Records','-dest',H+'/evidence/'+name+'-generated','-split-files','-emit-json',llbc]
if phase=='aeneas' and len(sys.argv)>4:
 cmd[1:1]=sys.argv[4:]
pins=ssh('python3 -c '+shlex.quote('import pathlib,hashlib,json;print(json.dumps({p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest() for p in '+repr([charon,charon+'-driver',aeneas,H+'/gate13/candidate/src/crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs']+([llbc] if phase=='aeneas' else [])+([H+'/gate13/candidate/src/tools/r1-builder-reference/records_reference.rs',H+'/gate13/candidate/src/tools/r1-builder-reference/pv_runjoin12_shipped.rs'] if phase=='charon' and len(sys.argv)>3 and sys.argv[3] in ['shipped-owned','shipped-owned-force'] else []))+'}))'))
expected_tools=json.loads((R/'evidence/pv-runjoin13-20261027/extractor-pins.json').read_text())
prior=json.loads((R/'evidence/pv-runjoin13-20261027/pv13-records-aeneas-02.json').read_text())['tool_source_pins']
for tool in [charon,charon+'-driver',aeneas]:
 assert json.loads(pins.stdout)[tool]==prior[tool], 'pinned extractor changed: '+tool
record=dict(name=name,phase=phase,command=cmd,tool_source_pins=json.loads(pins.stdout),worker_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),crate_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),opaque_child='pair_empty_roots must resolve to existing extracted implementation; no successful-child assumption',expected_time='optimized compilation then one records MIR translation' if phase=='charon' else 'one records Aeneas translation')
if phase=='charon' and len(sys.argv)>3 and sys.argv[3] in ['shipped-owned','shipped-owned-force']:record['adapter']='cfg(aeneas_ref) owned-argument borrow adapter calls original shipped records; no algorithm transcription; extraction not yet accepted'
(E/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
subprocess.run(['scp','-q',str(R/'tools/pv-runjoin11-20261027/kani-receipt.py'),f'{host}:{H}/evidence/pv12-extract-receipt.py'],check=True)
env=['env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','CARGO_TARGET_DIR='+H+'/target-charon','CARGO_BUILD_JOBS=4','CARGO_PROFILE_RELEASE_OPT_LEVEL=3','RUSTFLAGS=-C opt-level=3 -C link-arg=-Wl,--threads=4','PV8_SOURCE_DIR='+H+'/gate13/candidate/src']
scope=['systemd-run','--user','--scope','--quiet','--unit='+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64',*env,'python3',H+'/evidence/pv12-extract-receipt.py',H+'/evidence/'+name,'timeout','240',*cmd]
r=ssh(shlex.join(scope));(E/(name+'-scope.log')).write_text(r.stdout+r.stderr);print(r.stdout+r.stderr)
subprocess.run(['scp','-qr',f'{host}:{H}/evidence/{name}',str(E)],check=True)
if phase=='charon':subprocess.run(['scp','-q',f'{host}:{llbc}',str(E/(name+'.llbc'))],check=False)
else:subprocess.run(['scp','-qr',f'{host}:{H}/evidence/{name}-generated',str(E)],check=False)
receipt=E/name/'receipt.json'
d=json.loads(receipt.read_text());d.update(axioms='N/A: extraction, no Lean theorem',expected_time=record['expected_time'],source_revision=record['crate_revision'],worker_revision=record['worker_revision'],tool_source_pins=record['tool_source_pins']);receipt.write_text(json.dumps(d,indent=2)+'\n')
generated=E/(name+'-generated')/'translation.json'
if phase=='aeneas' and generated.exists():
 data=json.loads(generated.read_text());roots=[f for f in data.get('functions',[]) if f.get('rust_name','').endswith('::records') and not f.get('is_opaque',True)]
 (E/(name+'-acceptance.json')).write_text(json.dumps(dict(tool_exit=r.returncode,records_body_emitted=bool(roots),roots=roots,accepted_as_R_shipped=False,reason='kernel check and concrete helper links still required' if roots else 'no records definition emitted'),indent=2)+'\n')
print((E/name/'out.log').read_text()[-5000:])
sys.exit(r.returncode)
