# R555 zero-output programmed-oracle diagnostic: review plan only

Status: proposed patch prepared; **no compile or runtime launch is authorized yet**.

This is a fixed-seed diagnostic for the predeclared `recipient_zero` case in an isolated R117-derived copy. It does not establish a real SHA-256 attack, an admissible security-game witness, privacy failure, soundness failure, or any probability bound. Root retains game admissibility and all security interpretation.

## Frozen inputs and exact pins

- Selected source root: `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`.
- Frozen stage revision: `6677d5f1310ff7373301fbd79f186278f772e68a`.
- Selected Rust flags SHA-256: `df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8` (`R547 evidence/selected-rustflags.txt`). Append only `--cfg v8_semantic_rejoin`; retain overflow checks.
- Isolated destination proposed for approval: `/home/dombarker/project-offloads/aspis-r117-zero-output-rejoin-20261004-a`.
- R553 source capture pins are recorded in `../r553-zero-output-source-domain/manifest.json` and `SHA256SUMS`. Key hashes: raw verifier `d6dad89eaa8d735f467055e96a8df12de7a391e2475ec26c44b2bc493624a62a`; positivity fixture `3a19043d2f40f168cb2127ba46e1795db7ea0751625c4fe48c73e02dab533cab`; zero-output fixture `56fb063946c39602dc794f5ed9eaa0c705bf2ba9caabdf611dc3ffec4a6fd780`; public statement decoder/validator source `8b543d3de5aa29d1e510e8ca18bd2bc6dae6c405b7d6f97402c572dfdbab2588`.
- Candidate `performance.rs` starts byte-for-byte from the R547 recovery source (`54cbaf3fa4bb29f2e0e13b0663346b924fa184fc28d259644a3f77eb231e24f5`) and has only the proposed changes in `candidate/performance.diff` (SHA-256 `2c28ef2feea9aff546f238a0a6a590358e5ce4c9b6cac5d28567c7949b2b5ac2`). No verifier, positive-transfer relation, or oracle adapter source is changed by R555.
- Candidate build/run wrappers and exact diffs are `candidate/build-host.sh`, `candidate/build-host.diff`, `candidate/run-host.sh`, and `candidate/run-host.diff`. They target only the isolated root above and set `ASPIS_V8_POSITIVE_CASE=recipient_zero` for one `seed=1`.

To instantiate the candidate after approval, create the fresh copy from the frozen source and replay R547's exact host-only adapter/source edits from the saved R547 source snapshots (`source/relation_callback.rs`, `source/payment_extraction.rs`, and `source/semantic_rejoin_oracle.rs`), then apply the R555 `performance.diff`. Do not copy the already-built R547 worktree as the base and do not edit the frozen source.

## Proposed execution path and stop conditions

1. Use the existing `positive_transfer::case_compilation("recipient_zero", ...)` path. It rewrites only the intended witness/public outputs and transition. The existing private `positive_transfer::install` must return `Err(Error::Domain)` for the zero recipient cell. Record that the diagnostic producer bypassed only this honest-install refusal by setting the existing inverse cell; leave the selected verifier and its positivity terminal addition byte-identical.
2. Preserve all common binding/context checks and the existing `we::extract_checked` call. Require the actual checked extractor to reject this zero-output trace and print that result. Do not assert or imply that no alternate witness exists.
3. Before the oracle is armed, explicitly run the selected raw public decoder on the encoded rewritten public statement, run its typed public validator, compare the decoded value to the selected typed public, and raw-decode/compare the transition. A failure is recorded and stops the diagnostic; do not weaken any check.
4. Continue through the existing `semantic_negative_fixture`. Its `first_boundary_wrong` assertion must hold. Reuse R547's exact memoizing adapter and its post-round-zero hook: arm one fresh `state || 0x01` 33-byte preimage to zero, require first read by prover, reuse the exact immutable output on both selected verifier invocations and controls, SHA-256 for every other fresh input, and require sampled `z0=0`. No additional programming, seeds, nonce attempts, or challenge search.
5. Skip the old early error-4 negative stub only in this semantic-rejoin diagnostic, so it reaches existing complete C1/C2 encoding, commitment/authentication/opening construction, full body serialization, and both selected verifier entry points. Persist the body before final assertions. Keep all existing corruption, truncation, and noncanonical controls; retain R547's corrected expected programmed-entry counts (one prover read, two per selected verifier entry point, totals reported by the same adapter).
6. Run only if approved: offline/locked/release/jobs=1; full flags plus the R547 cfg; `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`; separate systemd user scopes with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. First compile the changed host target, then one fixed seed run. Do not run benchmarks or other cases.

## Source route behind the checks

The raw selected wrapper calls `decode_pool_v1_private_transfer_public_v1` before parsing the semantic body and reaches the selected verifier (`performance_verifier.rs:133-141`). The decoder checks the public byte framing and invokes `validate_pool_v1_private_transfer_public_v1` itself (`payment_relation.rs:376-413`); the typed validator checks common bindings and canonical commitments (`payment_relation.rs:182-230`). The transition decoder validates lengths, framing, reserved bytes, snapshot and afterstate, and their index relation (`pair_tree_profile.rs:583-637`). The R553 inventory documents that the typed public contains commitments, not the private amount cells. The selected verifier file stays unchanged.

The predeclared fixture writes recipient/change amounts into trace cells and rewrites commitments/output tree/afterstate (`selected_transfer_zero.rs:77-140`). Its own source validation passes the rewritten typed public and then reports checked trace extraction rejection (`selected_transfer_zero.rs:195-206`). Private install separately reads C1 cells 1014/1015 and returns `Domain` when either output is zero (`positive_transfer.rs:50-58`). These facts motivate the diagnostic plumbing only; they do not settle protocol witness legality.

## Exact candidate diff summary

`candidate/performance.diff` makes five changes only:

- Select and assert only `recipient_zero` under the existing diagnostic cfg.
- Add fail-closed raw/typed public and transition decoder checks before the programmed-oracle hook can be reached.
- Print the expected private-install refusal and checked-extractor result.
- Restrict R547's `+1` C1 mutation/extractor-success setup to the `honest` case, so this case does not mix that unrelated mutation into the zero-output trace.
- Let this configured diagnostic pass through the semantic fixture into full proof generation instead of taking the existing non-honest early error-4 stub.

No tests, compiles, runtime calls, proof generation, or verifier acceptance checks were run for R555 while preparing this plan.
