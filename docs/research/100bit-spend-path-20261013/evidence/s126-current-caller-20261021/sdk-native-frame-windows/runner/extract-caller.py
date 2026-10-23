#!/usr/bin/env python3
from pathlib import Path
import os,sys,subprocess,json,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
S=Path('/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src')
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release')
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
phase=sys.argv[1]; tag=sys.argv[2]; out=H/tag;out.mkdir(exist_ok=True)
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR='/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/charon-target',CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1')
for k in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(k,None)
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-'+phase+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
roots=['crate::verifier::candidate::tx1','crate::verifier::candidate::prepare']
layouts=['crate::transport::Variant','crate::verifier::View','crate::verifier::Prepared','crate::verifier::Error','crate::verifier::Phase','crate::verifier::Accumulator','aspis_core::field::WideExact','aspis_core::field::QM31','aspis_core::field::CM31','aspis_core::field::M31','aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public']
layouts += ['aspis_core::circle::SecureCirclePoint','aspis_core::field::wide_exact::WideExact','aspis_core::r0::Error',
 'aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1','aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1',
 'aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1',
 'aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1','aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1',
 'crate::compact::CodecError','crate::verifier::BatchedWeights','crate::verifier::QueryGeometry','crate::r1_semantic::Verified','crate::r1_wire::Error',
 'crate::r1_wire::Challenges','crate::r1_wire::SemanticTranscript']
roots += ['crate::verifier::mark']
if tag.startswith('prepared-'):
 roots += ['crate::verifier::_::new']
 layouts += ['crate::transcript::Transcript']
layouts += ['aspis_core::state_only_prefix::r0::Challenges']
roots += ['crate::compact::'+n for n in ['SPLIT','LOGICAL_SEMANTIC','LOGICAL_Y1','OFF_SEMANTIC','OFF_Y1','OFF_INACTIVE','OFF_FOLDED_ROOT','OFF_ROUND1']]
roots += ['aspis_core::field::wide_exact::_::ZERO']
if phase=='charon':
 cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err']
 for p in ['crate','aspis_core','aspis_statement']:cmd+=['--opaque',p]
 for p in roots:
  if '{' not in p and '_::new' not in p:cmd+=['--start-from',p]
  cmd+=['--include',p]
 for p in layouts:cmd+=['--include',p]
 cmd+=['--dest-file',str(out/'Caller.llbc'),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--locked','--offline','--release','--lib','--features','optimized-terminal,program-build','--jobs','1']
else:
 x=json.loads((out/'Caller.llbc').read_text());assert not x['has_errors']
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1CurrentCaller','-dest',str(out/'generated'),'-subdir','AspisR1CurrentCaller','-split-files','-emit-json',str(out/'Caller.llbc')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(out/(phase+'-input.json')).write_text(json.dumps(dict(command=cmd,roots=roots,layouts=layouts,source_revision='b2727acd3abf79315d18b754a260f58f4b1c6326',program_sources={str(p.relative_to(S)):sha(p) for p in (S/'crates/aspis-r1-cost-probe/src').glob('*.rs')},tool_pins={str(p):sha(p) for p in [T/'charon',T/'charon-driver',A]}),indent=2)+'\n')
os.chdir(S)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/(tag+'-'+phase)),'Release compilation and exact current tx1/prepare caller lowering; no arithmetic evaluation','--',*cmd]))
