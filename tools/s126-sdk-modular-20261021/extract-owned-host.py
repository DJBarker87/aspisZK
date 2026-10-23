#!/usr/bin/env python3
from pathlib import Path
import os,sys,subprocess,json,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');phase,tag=sys.argv[1:3];P=H/tag
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release');A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1')
for k in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(k,None)
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-'+phase+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
roots=['crate::owned_stage1_tail','crate::first_decoded','crate::observer','crate::decode_public_statement_box','crate::owned_checkpoint_nonzero']
layouts=['aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalCommonV1','aspis_statement::pool_v1::pair_forest_terminal::_::common','aspis_statement::pool_v1::pair_forest_terminal::_::semantic_public','aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public','aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1','aspis_r1_cost_probe::verifier::Error','aspis_r1_cost_probe::verifier::Phase','aspis_r1_cost_probe::transport::Variant','aspis_r1_cost_probe::transport::_::tag','core::option::Option','core::result::Result','core::result::_::map_err','solana_program_error::ProgramError']
layouts += ['aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1','aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1','aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1','aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31']
layouts += ['crate::SolanaDigest']
layouts += ['aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1','aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1']
layouts += ['aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestAccountErrorV1','aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError','aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementErrorV1','aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotErrorV1','aspis_statement::pool_v1::incremental_merkle::PoolV1TreeError']
if phase=='charon':
 cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default']
 for p in ['crate','aspis_core','aspis_statement','aspis_r1_cost_probe','solana_program_error']:cmd+=['--opaque',p]
 for p in roots:cmd+=['--start-from',p,'--include',p]
 for p in layouts:cmd+=['--include',p]
 cmd+=['--dest-file',str(P/'Owned.llbc'),'--','--manifest-path',str(P/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
else:
 x=json.loads((P/'Owned.llbc').read_text());assert not x['has_errors']
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisS2OwnedStage1','-dest',str(P/'generated'),'-subdir','AspisS2OwnedStage1','-split-files','-emit-json',str(P/'Owned.llbc')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(P/(phase+'-input.json')).write_text(json.dumps(dict(command=cmd,roots=roots,layouts=layouts,source_sha256=sha(P/'src/lib.rs'),tool_pins={str(p):sha(p) for p in [T/'charon',T/'charon-driver',A]}),indent=2)+'\n')
os.chdir(P)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/(tag+'-'+phase)),'Owned SDK stage1 tail translation: cached release compilation, no arithmetic evaluation','--',*cmd]))
