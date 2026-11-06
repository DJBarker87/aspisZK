from PCD_formal import *
import lzma,base64
features=['default','pair-forest-account-evidence','pair-forest-source-invariant-audit','pair-forest-source-result-invariant-audit','pair-forest-verifier-lane-invariant-audit','r1-split-checkpoint']
a=sys.argv[1] if len(sys.argv)>1 else 'PCD_K001'
args=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/PCD_src/programs/aspis-pool/Cargo.toml','--target-dir',B+'/PCD_target','--features',','.join(features),'--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness','pair_forest::PCD_harness::PCD_checked_rejection_contract','--output-format','terse']
if a=='PCD_K002':args=[v.replace('PCD_checked_rejection_contract','PCD_checked_rejection_control') for v in args]
x=dict(attempt=a,root_package='aspis-pool',metadata_features=','.join('aspis-pool/'+f for f in features),deployed_pool_features=features,native_command=args)
files={'PCD_native_gate.py':(E/'PCD_native_gate.py').read_text(),'PCD_native_config.json':json.dumps(x)}
repair=E/'PCD_NATIVE_REPAIR_FILES.json'
if repair.exists():files.update(json.loads(repair.read_text()))
env=json.loads((E.parent/'sdk-borrow-20261109/NLF_K060.json').read_text())['env']
env={k:v for k,v in env.items() if k in ['CARGO_PROFILE_DEV_OPT_LEVEL','CARGO_PROFILE_DEV_DEBUG','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','RUSTFLAGS']}
env['CARGO_PROFILE_RELEASE_OPT_LEVEL']='3'
env.update(CARGO_BUILD_JOBS='1',RUSTC_BOOTSTRAP='1',RUSTFLAGS='-Copt-level=3 -Ccodegen-units=1 -Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1',CARGO_PROFILE_DEV_CODEGEN_UNITS='1',CARGO_PROFILE_RELEASE_CODEGEN_UNITS='1',CARGO_PROFILE_DEV_BUILD_OVERRIDE_CODEGEN_UNITS='1',CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_CODEGEN_UNITS='1',CARGO_PROFILE_DEV_BUILD_OVERRIDE_OPT_LEVEL='3',CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL='3')
target='POOL:320 native checked-add rejection segment, arbitrary remaining fields (not a row root)'
(E/(a+'_PHASE.json')).write_text(json.dumps(dict(attempt=a,expected_phase=target,command=args,thread_limits='compiler/codegen/Rayon 1; unchanged TasksMax64'),indent=1)+'\n')
r=run(a,'kani',target,['python3','PCD_native_gate.py','PCD_native_config.json'],files,env)
# Recover bounded generated receipts (compressed metadata is copied read-only).
rr=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});names=list(b.glob({(a+'-*')!r}));out=[]
for p in names:
 if p.is_file() and ('metadata' in p.name or 'graph' in p.name or 'source-check' in p.name or 'lock-check' in p.name or 'tool-pins' in p.name):out.append(dict(name=p.name,data=base64.b64encode(p.read_bytes()).decode()))
print(json.dumps(out))
''');assert rr.returncode==0,rr.stderr
for q in json.loads(rr.stdout):(E/q['name']).write_bytes(base64.b64decode(q['data']))
print('Native child attempt recovered; credit requires the exact result, controls and domain review, never its exit status alone.')
