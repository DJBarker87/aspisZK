# Scratch reuse

LPi_src is a symlink to the previous LPf_src scratch (outside all git worktrees), reused after LPf terminated. No second corpus was copied. Prior LPf harness overlays remain exactly as recorded by LPf_harness.patch; LPi adds only its cfg(kani) module line and LPi_contracts.rs. No repository crates/ or programs/ file is written. The native scopes use the new LPi_target cache and private LPi_tmp directory.

LPi_run.py repairs only the job-owned metadata parser: locate the JSON object after preceding cargo diagnostics, then validate all package tuples and edges and exact normalized graph equality. Metadata still uses --locked --offline. cargo-kani omits unsupported --locked, sets CARGO_NET_OFFLINE=true and checks the frozen Cargo.lock hash before/after every proof. The S2W and reservation infrastructure are unchanged.

K001 codegen rejected the combination of the inherited LPf function-contract instrumentation with an ordinary kani::stub for M31::to_le_bytes (missing __kani_recursion_check_to_le_bytes). No solver ran. Replaced the scratch overlay with exact frozen release bytes at 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, plus only the LPi cfg(kani) module. All six changed scratch source/lock hashes are in LPi_overlay_reset.json. This fixes only this job’s harness overlay, with no launcher change or shipped edit.

Final packaging retains harnesses only as exact per-run patches plus receipts. Loose Rust/frozen-source upload copies were removed. LPi_sync.py now reconstructs only the two added modules from the final patch and performs the same admission gate, with an additional full frozen-source audit. Reconstruction was checked byte-for-byte against the uploaded source; no additional prover ran.
