from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended')
S=B/'PCD_request_ref'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=['crate::request_ref']
namespace='PCD_FrozenRequest'
dest=B/'PCD_request_extracted'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--include','aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestLaneStateV1','--include','aspis_statement::pool_v1::incremental_merkle::IncrementalMerkleTreeV1','--include','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalResultV1','--include','aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1','--include','aspis_core::field::M31','--include','solana_program_error::ProgramError','--include','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalRequestV1','--include','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalPaymentV1','--include','aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1','--include','aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1']
for root in roots:cmd+=['--start-from',root]
cmd+=['--dest-file',str(B/'PCD_request_ref.llbc'),'--','--manifest-path',str(S/'Cargo.toml'),'--offline','--locked','--release','--lib','--jobs','1']

env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'PCD_actual_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),rust_reference_sha256=sha(S/'src/lib.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',aeneas_origin='b59d5188 extended binary; imported read-only, no tool patches by NCO')
(B/'PCD_REF_CHARON_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(pins),flush=True)
before=sha(S/'Cargo.lock')
application_lock_before=sha(B/'PCD_src/Cargo.lock')
r=subprocess.run(cmd,cwd=S,env=env)
assert sha(S/'Cargo.lock')==before,'STOP reference lock drift'
assert sha(B/'PCD_src/Cargo.lock')==application_lock_before=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','STOP application lock drift'
if r.returncode:raise SystemExit(r.returncode)
pins.update(charon_exit=r.returncode,llbc_sha256=sha(B/'PCD_request_ref.llbc') if (B/'PCD_request_ref.llbc').exists() else None,phase='Charon ONLY after separately compiled dependency; no Aeneas in this scope')
(B/'PCD_REF_CHARON_PINS.json').write_text(json.dumps(pins,indent=2))
raise SystemExit(r.returncode)
