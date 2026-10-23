#!/usr/bin/env python3
"""Extract actual frozen full-forest outer encoder, preserving full carriers.
Nested validation/codec functions are explicit child boundaries, not closed.
No source rewrite, reference carrier or SDK/execution claim.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s6-full-forest-codec-all-v1';phase=sys.argv[1];assert phase in ['charon','aeneas']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if phase=='charon':
 P.mkdir(exist_ok=False);source=H/'aspis-s6-native-semantic-projection-v1'
 # Reuse the immutable current-codec dependency and its warm build path.
 reused=H/'s6-full-forest-codec-extract-v3/frozen-source/crates/aspis-statement'
 shutil.copyfile(source/'frozen-statement-binding.json',P/'frozen-statement-binding.json')
 (P/'input').mkdir()
 (P/'input/Cargo.toml').write_text('''[package]
name="aspis-s6-full-forest-encoder-extract"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
aspis-statement={path="/home/dombarker/project-offloads/s126-real-sdk-20261021/s6-full-forest-codec-extract-v3/frozen-source/crates/aspis-statement",features=["r0"]}
[lib]
path="lib.rs"
[profile.release]
opt-level=3
overflow-checks=true
''')
 (P/'input/lib.rs').write_text('''pub fn encode(statement:&aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1)->Result<[u8;1880],aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1>{aspis_statement::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_statement_v1(statement)}\n''')
 with (P/'input/lib.rs').open('a') as f:f.write('pub fn decode(bytes:&[u8])->Result<aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1,aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1>{aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1(bytes)}\n')
 T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
 opaque=[]
 cmd=[str(T),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err','--include','aspis_statement::*','--include','aspis_core::field::*','--start-from','crate::encode','--start-from','crate::decode',*sum((['--opaque',p] for p in opaque),[]),'--dest-file',str(P/'Codec.llbc'),'--','--manifest-path',str(P/'input/Cargo.toml'),'--offline','--release','--lib','--jobs','1']
 (P/'opaque-children.json').write_text(json.dumps(opaque,indent=2)+'\n')
else:
 assert not json.loads((P/'Codec.llbc').read_text())['has_errors']
 A=H/'s1-collapse-tool-recover-v2/source/src/_build/default/main.exe'
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS6AllForestCodec','-dest',str(P/'generated'),'-subdir','AspisS6AllForestCodec','-split-files','-emit-json',str(P/'Codec.llbc')]
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
tag='s6-full-forest-codec-all-'+phase+'-v1'
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,source_sha256=sha(P/'input/lib.rs'),tool_sha256=sha(Path(cmd[0])),llbc_sha256=sha(P/'Codec.llbc') if phase=='aeneas' else None,qualification=__doc__,expected_time='Focused cached optimized full native forest codec extraction, no opaque codec/validator children; no arithmetic evaluation. Explicitly inspect any remaining external std functions.'),indent=2)+'\n')
os.chdir(P/'input')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Full native forest codec source exploration, all reachable statement/field bodies included','--','timeout','180',*cmd]))
