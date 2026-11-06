from PCD_formal import *
import base64
features=['default','pair-forest-account-evidence','pair-forest-source-invariant-audit','pair-forest-source-result-invariant-audit','pair-forest-verifier-lane-invariant-audit','r1-split-checkpoint']
a=sys.argv[1]
harnesses={
 'PCD_K002':'PCD_checked_rejection_control','PCD_K008':'PCD_checked_rejection_control','PCD_K012':'PCD_checked_rejection_control',
 'PCD_K009':'PCD_frontier_contract','PCD_K010':'PCD_frontier_control','PCD_K013':'PCD_frontier_contract','PCD_K014':'PCD_frontier_control',
 'PCD_K015':'PCD_frontier_contract','PCD_K016':'PCD_frontier_control','PCD_K019':'PCD_frontier_contract','PCD_K020':'PCD_frontier_control',
 'PCD_K017':'PCD_finish_contract','PCD_K018':'PCD_finish_control'}
harness=harnesses.get(a,'PCD_checked_rejection_contract')
frontier=harness.startswith('PCD_frontier_')
args=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/PCD_src/programs/aspis-pool/Cargo.toml','--target-dir',B+'/PCD_target','--features',','.join(features),'--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness','pair_forest::PCD_harness::'+harness,'--output-format','terse']
if a=='PCD_K004':args+=['--only-codegen']
else:args+=['--unwind',('33' if a in {'PCD_K015','PCD_K016','PCD_K019','PCD_K020'} else '10') if frontier else '1','--verbose']
x=dict(attempt=a,root_package='aspis-pool',metadata_features=','.join('aspis-pool/'+f for f in features),deployed_pool_features=features,native_command=args,expected_harness='pair_forest::PCD_harness::'+harness)
files={'PCD_native_gate.py':(E/'PCD_native_gate.py').read_text(),'PCD_native_config.json':json.dumps(x)}
files.update(json.loads((E/'PCD_NATIVE_REPAIR_FILES.json').read_text()))
env=dict(CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_PROFILE_RELEASE_OPT_LEVEL='3',CARGO_BUILD_JOBS='1',RUSTC_BOOTSTRAP='1',RUSTFLAGS='-Copt-level=3 -Ccodegen-units=1 -Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1',CARGO_PROFILE_DEV_CODEGEN_UNITS='1',CARGO_PROFILE_RELEASE_CODEGEN_UNITS='1',CARGO_PROFILE_DEV_BUILD_OVERRIDE_CODEGEN_UNITS='1',CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_CODEGEN_UNITS='1',CARGO_PROFILE_DEV_BUILD_OVERRIDE_OPT_LEVEL='3',CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL='3')
target='POOL:320 post-loop returned record at one arbitrary scalar observer' if a in {'PCD_K017','PCD_K018'} else 'POOL:320 one native frontier iteration at arbitrary pre-state/level (source-segment candidate)' if frontier else 'POOL:320 actual frozen checked-add rejection segment, arbitrary remaining fields (not a row root)'
(E/(a+'_PHASE.json')).write_text(json.dumps(dict(attempt=a,expected_phase='optimized compilation then CBMC: '+target,command=args),indent=1)+'\n')
r=run(a,'kani',target,['python3','PCD_native_gate.py','PCD_native_config.json'],files,env)
rr=ssh('python3',f'''from pathlib import Path
import json,base64,hashlib
b=Path({B!r});lock=b/'PCD_src/Cargo.lock';h=hashlib.sha256(lock.read_bytes()).hexdigest();frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
(b/{(a+'-lock-recovery.json')!r}).write_text(json.dumps(dict(before=frozen,after=h,unchanged=h==frozen,recovered_after_scope=True),indent=1)+'\\n');assert h==frozen,'STOP lock drift'
names=[p for p in b.glob({(a+'-*')!r}) if p.is_file() and any(k in p.name for k in ['metadata','graph','source-check','lock','tool-pins','fragment'])]
print(json.dumps([dict(name=p.name,data=base64.b64encode(p.read_bytes()).decode()) for p in names]))
''');assert rr.returncode==0,rr.stderr
for q in json.loads(rr.stdout):(E/q['name']).write_bytes(base64.b64decode(q['data']))
print('PCD native receipt and strict post-scope lock recovered; credit requires semantic verdict and controls.')
sys.exit(r['exit_status'])
