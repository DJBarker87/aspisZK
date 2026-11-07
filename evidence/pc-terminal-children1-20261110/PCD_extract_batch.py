from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended')
S=B/'PCD_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=['crate::pair_forest::next_lane_image_box_v1','crate::pair_forest::decode_terminal_checkpoint_box_v1','crate::pair_forest::decode_terminal_lane_box_v1','crate::pair_forest::decode_terminal_master_box_v1','crate::pair_forest::validate_authenticated_terminal_result_v1']
namespace='PCD_TerminalBatch'
dest=B/'PCD_request_extracted'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--include','aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestLaneStateV1','--include','aspis_statement::pool_v1::incremental_merkle::IncrementalMerkleTreeV1','--include','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalResultV1','--include','aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1','--include','aspis_core::field::M31','--include','solana_program_error::ProgramError','--include','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalRequestV1','--include','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalPaymentV1','--include','aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1','--include','aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1']
for root in roots:cmd+=['--start-from',root]
for child in ['next_pair_forest_lane_v1','encode_lane_from_authenticated_result_v1','decode_retained_pair_forest_checkpoint_account_v1','decode_lane_account_from_program_invariant_v1','decode_master_account','terminal_common_box_v1','transfer_terminal_statement_box_v1','withdrawal_terminal_statement_box_v1']:
 cmd+=['--exclude','crate::pair_forest::'+child]
cmd+=['--dest-file',str(B/'PCD_terminal_batch.llbc'),'--','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'--offline','--locked','--release','--lib','--jobs','1','--features','default,pair-forest-account-evidence,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit,pair-forest-verifier-lane-invariant-audit,r1-split-checkpoint']

env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'PCD_actual_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),rust_reference_sha256=sha(S/'programs/aspis-pool/src/pair_forest.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',aeneas_origin='b59d5188 extended binary; imported read-only, no tool patches by NCO')
(B/'PCD_BATCH_CHARON_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=S,env=env)
if r.returncode:assert r.returncode==0
pins.update(charon_exit=r.returncode,llbc_sha256=sha(B/'PCD_terminal_batch.llbc') if (B/'PCD_terminal_batch.llbc').exists() else None,phase='Charon ONLY after separately compiled dependency; no Aeneas in this scope')
(B/'PCD_BATCH_CHARON_PINS.json').write_text(json.dumps(pins,indent=2))
assert r.returncode==0

cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PCD_TerminalBatch','-dest',str(B/'PCD_terminal_batch_extracted'),'-subdir','PCD_TerminalBatch','-split-files',str(B/'PCD_terminal_batch.llbc')]
r=subprocess.run(cmd,cwd=B)
(B/'PCD_BATCH_AENEAS_PINS.json').write_text(json.dumps(dict(aeneas_sha256=sha(A),llbc_sha256=sha(B/'PCD_terminal_batch.llbc'),command=cmd,exit=r.returncode,outputs={str(q.relative_to(B)):sha(q) for q in (B/'PCD_terminal_batch_extracted').rglob('*') if q.is_file()}),indent=1)+'\n')
raise SystemExit(r.returncode)
