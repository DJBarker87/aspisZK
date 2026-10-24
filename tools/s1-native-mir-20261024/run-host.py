#!/usr/bin/env python3
"""New MIR-stage probe of unchanged original claim, fresh capped admission."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
original=Path('/home/dombarker/project-offloads/s1-current-claim-extraction-v2-20261020/input')
base=H/'s1-native-mir-20261024';base.mkdir(exist_ok=True)
stage,phase=sys.argv[1:3];assert stage in ['promoted','elaborated','optimized'] and phase in ['charon','aeneas']
work=base/stage;work.mkdir(exist_ok=True);source=work/'input'
if not source.exists():shutil.copytree(original,source)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((source/'source-pins.json').read_text())
for path,expected in pins['kit_files'].items():assert sha(source/path)==sha(original/path)==expected,path
name='s1-original-mir-'+stage+'-'+phase+'-v1';out=base/name;out.mkdir(exist_ok=False)
subprocess.run(['python3',str(H/'kit/reservation.py'),str(out/'admission-app-scopes.json')],check=True,stdout=subprocess.DEVNULL)
collector=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py')
snapshot=subprocess.check_output(['python3',str(collector)],text=True);(out/'admission-global.json').write_text(snapshot)
inv=json.loads(snapshot);G=2**30;assert inv['effective_sum_bytes']+3*G<=48*G and inv['MemAvailable_kB']*1024>=6*G,'Fresh global admission denied; no job launched'
charon=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
aeneas=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
llbc=work/'OriginalClaim.llbc'
if phase=='charon':
 cmd=[str(charon),'cargo','--preset','aeneas','--mir',stage,'--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err','--start-from','crate::verifier::prepared_claim']
 for path in pins['opaque_paths']:cmd+=['--opaque',path]
 cmd+=['--dest-file',str(llbc),'--','--locked','--offline','--release','--lib','--no-default-features','--features','r0,private-leaf-salts','--jobs','1']
else:
 assert llbc.exists() and not json.loads(llbc.read_text())['has_errors']
 cmd=[str(aeneas),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisR1OriginalMirClaim','-dest',str(work/'generated'),'-subdir','AspisR1OriginalMirClaim','-split-files','-emit-json',str(llbc)]
env=dict(os.environ);env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(work/'target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for key in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(key,None)
meta=dict(schema='focused-extractor-proof-packet-v1',stage=stage,phase=phase,command=cmd,source_pins=pins,source_pins_sha256=sha(source/'source-pins.json'),tool_sha256={str(p):sha(p) for p in [charon,charon.with_name('charon-driver'),aeneas,Path(__file__)]},environment={k:env[k] for k in ['RUSTUP_TOOLCHAIN','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']},expected_time='Small source-cut compilation/Charon lowering, then original nested-loop Aeneas translation; no arithmetic gate or proof generation.',qualification='Unchanged original Rust input and ABI; only MIR stage changes. Not source refinement or closure until emitted body, imports and source pins are checked.')
(out/'input.json').write_text(json.dumps(meta,indent=2)+'\n')
os.chdir(source)
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=2G','-p','MemoryMax=3G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(out/'attempt'),meta['expected_time'],'--','timeout','120',*cmd],env=env)
unchanged={p:sha(source/p)==expected for p,expected in pins['kit_files'].items()};assert all(unchanged.values())
(out/'source-postcheck.json').write_text(json.dumps(dict(unchanged=unchanged,exit_status=status),indent=2)+'\n')
print(json.dumps(dict(name=name,exit_status=status,output=str(out))))
raise SystemExit(status)
