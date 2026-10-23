#!/usr/bin/env python3
"""Focused actual full-carrier owned frontier reference. Digest is its one leaf."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s6-snapshot-loop-parent-extract-v2';K=P/'input';phase=sys.argv[1];assert phase in ['charon','aeneas'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((H/'receipts/s6-native-snapshot-helper-v1/receipt.json').read_text())['exit_status']==0,'Native predecessor must pass first'
if phase=='charon':
 P.mkdir(exist_ok=False)
 import shutil
 base=H/'aspis-s6-native-snapshot-helper-v1'
 shutil.copytree(base/'frozen-source',P/'frozen-source');K.mkdir()
 m=json.loads((base/'source-manifest.json').read_text())
 target=P/'frozen-source/crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';original=target.read_text()
 fragment=m['original_loop_fragment'];assert original.count(fragment)==1
 helpers=(m['step_helper']+m['helper_loop']).replace('pub fn frontier_step','fn frontier_step_reference').replace('pub fn frontier_loop','fn frontier_loop_reference').replace('frontier_step(snapshot','frontier_step_reference(snapshot').replace('Snapshot','PoolV1PairLiveSnapshotV1')
 target.write_text(original.replace(fragment,'frontier_loop_reference(snapshot, output);',1)+'\n'+helpers)
 (P/'source-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',original_loop=fragment,replacement='frontier_loop_reference(snapshot, output);',helpers=helpers,predecessor='s6-native-snapshot-helper-v1',original_file_sha256=__import__('hashlib').sha256(original.encode()).hexdigest(),candidate_file_sha256=sha(target),qualification='Only original foreach replaced by the exact checked full-native helper loop, names/native type alias restored. Original validation/header/errors unchanged. Two source child leaves must be installed, original validator has separate native equivalence evidence. No production adoption or SDK/contextual closure.'),indent=2)+'\n')
 (K/'Cargo.toml').write_text('[package]\nname="aspis-s6-snapshot-loop-parent"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[dependencies]\naspis-statement={path="../frozen-source/crates/aspis-statement",features=["r0"]}\n[lib]\npath="lib.rs"\n[profile.release]\nopt-level=3\noverflow-checks=true\n')
 (K/'lib.rs').write_text('pub fn encode(snapshot:&aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1,output:&mut[u8])->Result<(),aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotErrorV1>{aspis_statement::pool_v1::pair_tree_profile::encode_pool_v1_pair_live_snapshot_v1(snapshot,output)}\n')
 T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
 cmd=[str(T),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','aspis_statement::*','--include','aspis_core::field::*','--opaque','aspis_statement::atomic_statement::encode_digest_canonical','--opaque','aspis_statement::pool_v1::pair_tree_profile::validate_pool_v1_pair_live_snapshot_v1','--start-from','crate::encode','--dest-file',str(P/'Snapshot.llbc'),'--','--manifest-path',str(K/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
else:
 assert not json.loads((P/'Snapshot.llbc').read_text())['has_errors']
 T=H/'s6-formatter-tool-v5/source/src/_build/default/main.exe'
 cmd=[str(T),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS6SnapshotLoopParent','-dest',str(P/'generated'),'-subdir','AspisS6SnapshotLoopParent','-split-files','-emit-json',str(P/'Snapshot.llbc')]
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
tag='s6-snapshot-loop-parent-'+phase+'-v2';collector=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py')
inv=json.loads(subprocess.check_output(['python3',str(collector)],text=True));(H/(tag+'-global-admission.json')).write_text(json.dumps(inv,indent=2)+'\n');assert inv['effective_sum_bytes']+2*2**30<=48*2**30 and inv['MemAvailable_kB']*1024>=4*2**30,'Global admission denied'
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,tool_sha256=sha(T),source_sha256=sha(K/'lib.rs'),cargo_sha256=sha(K/'Cargo.toml'),llbc_sha256=sha(P/'Snapshot.llbc') if phase=='aeneas' else None,qualification=__doc__,expected_time='Focused cached optimized Rust/Charon or small Aeneas helper/loop extraction; no complete codec replay. High1G/Max2G/Swap0. Concrete native types retained; one digest leaf will be installed from the checked actual reference.'),indent=2)+'\n')
os.chdir(K);raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Focused full-native frontier helper and loop; no arithmetic generation','--','timeout','180',*cmd]))
