#!/usr/bin/env python3
"""Extract unchanged full forest encoder and validator; install four concrete verified source children."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s6-forest-parent-extract-v1';K=P/'input';phase=sys.argv[1];assert phase in ['charon','aeneas'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if phase=='charon':
 P.mkdir(exist_ok=False);K.mkdir()
 import shutil
 shutil.copytree(H/'aspis-s6-native-snapshot-helper-v1/frozen-source',P/'frozen-source')
 (K/'Cargo.toml').write_text('[package]\nname="aspis-s6-forest-parent"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[dependencies]\naspis-statement={path="../frozen-source/crates/aspis-statement",features=["r0"]}\n[lib]\npath="lib.rs"\n[profile.release]\nopt-level=3\noverflow-checks=true\n')
 (K/'lib.rs').write_text('pub fn encode(statement:&aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1)->Result<[u8;1880],aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1>{aspis_statement::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_statement_v1(statement)}\n')
 T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
 cmd=[str(T),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','aspis_statement::*','--include','aspis_core::field::*','--include','core::result::_::map_err','--opaque','aspis_statement::pool_v1::pair_tree_profile::encode_pool_v1_pair_late_public_statement_v1','--opaque','aspis_statement::pool_v1::payment_relation::encode_pool_v1_private_transfer_public_v1','--opaque','aspis_statement::pool_v1::payment_relation::encode_pool_v1_withdrawal_public_v1','--opaque','aspis_statement::atomic_statement::encode_digest_canonical','--start-from','crate::encode','--dest-file',str(P/'Forest.llbc'),'--','--manifest-path',str(K/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
else:
 assert not json.loads((P/'Forest.llbc').read_text())['has_errors']
 T=H/'s6-formatter-tool-v5/source/src/_build/default/main.exe'
 cmd=[str(T),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS6ForestParent','-dest',str(P/'generated'),'-subdir','AspisS6ForestParent','-split-files','-emit-json',str(P/'Forest.llbc')]
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
tag='s6-forest-parent-'+phase+'-v1';collector=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py')
inv=json.loads(subprocess.check_output(['python3',str(collector)],text=True));(H/(tag+'-global-admission.json')).write_text(json.dumps(inv,indent=2)+'\n');assert inv['effective_sum_bytes']+2*2**30<=48*2**30 and inv['MemAvailable_kB']*1024>=4*2**30,'Global admission denied'
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,tool_sha256=sha(T),source_sha256=sha(K/'lib.rs'),cargo_sha256=sha(K/'Cargo.toml'),llbc_sha256=sha(P/'Forest.llbc') if phase=='aeneas' else None,qualification=__doc__,expected_time='Focused cached optimized Rust/Charon or small Aeneas helper/loop extraction; no complete codec replay. High1G/Max2G/Swap0. Full native types retained; actual concrete payment, late encoder references and digest installed. Frozen source body unchanged; prior reference transformation transport remains open.'),indent=2)+'\n')
os.chdir(K);raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Focused full native forest encoder/validator extraction; no arithmetic generation','--','timeout','180',*cmd]))
