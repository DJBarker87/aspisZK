#!/usr/bin/env python3
"""Focused actual full-carrier owned frontier reference. Digest is its one leaf."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s6-late-parent-extract-v1';K=P/'input';phase=sys.argv[1];assert phase in ['charon','aeneas'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if phase=='charon':
 P.mkdir(exist_ok=False);K.mkdir()
 import shutil
 shutil.copytree(H/'aspis-s6-native-snapshot-helper-v1/frozen-source',P/'frozen-source')
 (K/'Cargo.toml').write_text('[package]\nname="aspis-s6-late-parent"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[dependencies]\naspis-statement={path="../frozen-source/crates/aspis-statement",features=["r0"]}\n[lib]\npath="lib.rs"\n[profile.release]\nopt-level=3\noverflow-checks=true\n')
 (K/'lib.rs').write_text('pub fn encode(statement:&aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1,output:&mut[u8])->Result<(),aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementErrorV1>{aspis_statement::pool_v1::pair_tree_profile::encode_pool_v1_pair_late_public_statement_v1(statement,output)}\n')
 T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
 cmd=[str(T),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','aspis_statement::*','--include','aspis_core::field::*','--include','core::result::_::map_err','--opaque','aspis_statement::pool_v1::pair_tree_profile::encode_pool_v1_pair_live_snapshot_v1','--opaque','aspis_statement::pool_v1::pair_terminal::encode_pool_v1_pair_verified_afterstate_v1','--start-from','crate::encode','--dest-file',str(P/'Late.llbc'),'--','--manifest-path',str(K/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
else:
 assert not json.loads((P/'Late.llbc').read_text())['has_errors']
 T=H/'s6-formatter-tool-v5/source/src/_build/default/main.exe'
 cmd=[str(T),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS6LateParent','-dest',str(P/'generated'),'-subdir','AspisS6LateParent','-split-files','-emit-json',str(P/'Late.llbc')]
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
tag='s6-late-parent-'+phase+'-v1';collector=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py')
inv=json.loads(subprocess.check_output(['python3',str(collector)],text=True));(H/(tag+'-global-admission.json')).write_text(json.dumps(inv,indent=2)+'\n');assert inv['effective_sum_bytes']+2*2**30<=48*2**30 and inv['MemAvailable_kB']*1024>=4*2**30,'Global admission denied'
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,tool_sha256=sha(T),source_sha256=sha(K/'lib.rs'),cargo_sha256=sha(K/'Cargo.toml'),llbc_sha256=sha(P/'Late.llbc') if phase=='aeneas' else None,qualification=__doc__,expected_time='Focused cached optimized Rust/Charon or small Aeneas helper/loop extraction; no complete codec replay. High1G/Max2G/Swap0. Concrete native types retained; one digest leaf will be installed from the checked actual reference.'),indent=2)+'\n')
os.chdir(K);raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Focused full-native frontier helper and loop; no arithmetic generation','--','timeout','180',*cmd]))
