#!/usr/bin/env python3
"""Extract the complete Kani-coupled owned Y1 body, not a scalar carrier."""
from pathlib import Path
import os,sys,json,subprocess,hashlib,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');W=H/'s1-y1-owned-extraction-v3-20261024';P=H/'s1-y1-native-v5-20261024'
phase=sys.argv[1];assert phase in ['charon','aeneas']
if phase=='charon':
 W.mkdir(exist_ok=False);shutil.copytree(P/'src',W/'src')
 for f in ['Cargo.toml','Cargo.lock','source-binding.json']:shutil.copyfile(P/f,W/f)
 proof=json.loads((P/'shipped_y1_vec_owned_equivalent-receipt/receipt.json').read_text());assert proof['exit_status']==0
else:assert not json.loads((W/'Y1Owned.llbc').read_text())['has_errors']
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release');A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(H/'kit/reservation.py'),str(W/(phase+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
snap=subprocess.check_output(['python3','/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py'],text=True);(W/(phase+'-global-admission.json')).write_text(snap);ad=json.loads(snap);G=2**30
assert ad['effective_sum_bytes']+8*G<=48*G and ad['MemAvailable_kB']*1024>=14*G,'fresh global admission refused'
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
if phase=='charon':
 cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--start-from','crate::values_owned_reference','--include','crate::values_owned_reference','--include','crate::copy_chunk','--include','crate::read_input','--include','crate::write_output','--include','crate::CodecError','--dest-file',str(W/'Y1Owned.llbc'),'--','--manifest-path',str(W/'Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1']
else:
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS1ValuesOwned','-dest',str(W/'generated'),'-subdir','AspisS1ValuesOwned','-split-files','-emit-json',str(W/'Y1Owned.llbc')]
meta={'schema':'focused-extractor-proof-packet-v1','command':cmd,'source_sha256':sha(W/'src/lib.rs'),'source_binding':json.loads((W/'source-binding.json').read_text()),'kani_equivalence_receipt':proof if phase=='charon' else json.loads((P/'shipped_y1_vec_owned_equivalent-receipt/receipt.json').read_text()),'tools':{str(p):sha(p) for p in [T/'charon',T/'charon-driver',A]},'runner_sha256':sha(Path(__file__)),'llbc_sha256':sha(W/'Y1Owned.llbc') if phase=='aeneas' else None,'expected_time':'Small optimized standalone Rust source extraction, then Aeneas translation of two owned array loops; no cryptographic arithmetic or elimination.','qualification':'Complete owned Y1 reference, with separate unchanged native fixed-Y1 Kani equality. No production adoption or whole SDK/caller closure.'}
(W/(phase+'-input.json')).write_text(json.dumps(meta,indent=2)+'\n');os.chdir(W)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(W/(phase+'-receipt')),'Optimized small owned Y1 source extraction/translation; not arithmetic generation','--','timeout','180',*cmd]))
