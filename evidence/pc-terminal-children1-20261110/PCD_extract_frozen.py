from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended')
S=B/'PCD_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=['crate::pair_forest::next_pair_forest_lane_v1']
namespace='PCD_FrozenLane'
dest=B/'PCD_frozen_extracted'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--include','aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestLaneStateV1','--include','aspis_statement::pool_v1::incremental_merkle::IncrementalMerkleTreeV1','--include','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalResultV1','--include','aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1','--include','aspis_core::field::M31','--include','solana_program_error::ProgramError']
for root in roots:cmd+=['--start-from',root]
cmd+=['--dest-file',str(B/'PCD_frozen_lane.llbc'),'--','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'--offline','--locked','--release','--lib','--jobs','1','--features','default,pair-forest-account-evidence,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit,pair-forest-verifier-lane-invariant-audit,r1-split-checkpoint']

env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'PCD_actual_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),rust_reference_sha256=sha(S/'programs/aspis-pool/src/pair_forest.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',aeneas_origin='b59d5188 extended binary; imported read-only, no tool patches by NCO')
(B/'PCD_FROZEN_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=S,env=env)
if r.returncode:raise SystemExit(r.returncode)
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',namespace,'-dest',str(dest),'-subdir',namespace,'-split-files',str(B/'PCD_frozen_lane.llbc')]
print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env)
pins.update(aeneas_command=cmd,exit=r.returncode,outputs={str(p.relative_to(B)):sha(p) for p in dest.rglob('*') if p.is_file()})
(B/'PCD_FROZEN_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
raise SystemExit(r.returncode)
