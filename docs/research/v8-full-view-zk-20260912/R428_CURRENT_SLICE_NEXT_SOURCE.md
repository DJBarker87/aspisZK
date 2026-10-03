# R428: concrete slice-next source capture

This milestone exposes the concrete standard-library `next` body behind the R327 normalization-helper receiver frontier. It is source evidence, not a Lean execution proof and not the actual `QM31` freeze-fold binding.

## Exact scope and result

- Requested root: `crate::circle_norm::joined_inverse::line_norm::r110_norm::batch`.
- Actual captured iterator specialization: `core::slice::iter::Iter<B>`, where this helper defines `struct B(u32);`. Its captured x86_64 layout is size 4/alignment 4. Do not describe this specialization as `QM31`.
- Starting plan: complete R327 command SHA256 `021c55ed604170e5982365f714d4abd46edf4b14ad0d626b1c59d25f8b6da1ad`; append only `--include core::slice::iter::_::next` and change the output destination. Preserve monomorphization, all previous ordered includes, frozen sources, optimized Rustflags, features and offline/locked release settings.
- Original Charon source commit: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`, tracked sources clean before/after. Original wrapper SHA256 `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`; original driver SHA256 `4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938`. No observer hook or translator repair was used.
- Rustc: pinned nightly-2026-06-01, commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.
- Launch worktree revision: `09b9bef079186b1b34354c4c5519b79d3a8ff096`. The old R327 source-revision label is historical; seven exact current frozen-source hashes and four standard-library source hashes are recorded before and after this capture.
- Charon exit 0; GNU time exit 0; LLBC `has_errors=false`; wall time 14.65 seconds; peak RSS 628,696 KiB; swaps 0.
- Actual cgroup limits before/after: MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128. Resource reservation, peak memory, swap and memory events are saved in the host receipts. No other heavy job was running at launch.
- Output SHA256: `b96970e5b338b11db1120fddbcf75a1f70dbba2a322de9c72f37d9d57c30ed62`.
- Complete `#print axioms`: not applicable. No Lean file or theorem was compiled in this milestone.

## Verified evidence boundary

The native LLBC now records function 10 as Transparent with a Structured body, rather than the prior opaque row. The body preserves the standard-library zero-sized and ordinary-element paths, receiver field accesses, pointer operations, stopping tests and returned old-element reference. Capturing these operations does not prove pointer validity, aliasing or source-to-model execution. In particular, the extracted `IS_ZST` global refers to an initializer call; this capture must not silently substitute a Boolean constant or discard a branch.

The existing R183/R319 equations for the defined Aeneas slice model remain valid and are not rerun. They do not by themselves prove this Rust implementation, the native copied mutable call argument, or a replacement reborrow lowering. This extraction changes source-selection scope, not verifier source or security parameters. The genuine 999,790 / 999,532 CU results remain preserved; no CU benchmark or unchanged regression was repeated.

The earlier R327-derived agent launcher drafts were incomplete and never launched. They remain in scratch. The actual root-owned launcher, materialized remote script, exact command, full logs, receipts, collected source output and audits are saved here. No failed extraction was retried in this milestone. The launcher checks user Aspis units and all-user named heavy processes, plus available memory; it does not enumerate system-level service memory caps. This reservation evidence limit must remain explicit. Its stale-output collection path would need a fail-closed check for a preexisting remote destination; the actual fresh-destination assertion passed in this attempt, so the saved output is from this invocation. The next launcher must address both issues. The complete base extract-command pins every actual argument and Rustflag; the old auxiliary launch-plan was not a runtime input.

## First remaining proposition

Bind the actual selected `freeze` iterator specialization and execution to the existing model, preserving source slice validity, pointer/cursor correspondence, element layout, the returned reference's original slice lifetime, receiver updates and caller reuse, stopping, errors and ownership. A helper `Iter<B>` capture cannot close the `QM31` freeze gate. Before any receiver repair is accepted, its source preservation must be proved without assuming a whole standard-library contract or replacing mutable Copy with Move.

The existing actual freeze R185 extraction leaves specialized slice `fold` at function 70 opaque. The pinned macro implementation (macros.rs259–289) consumes the iterator and uses an index loop with a closure call; it does not delegate to `next`. Expose and prove that actual specialization next, preserving the closure's captured gamma power. Do not substitute the helper's `try_fold` receiver argument for this missing fold proof. Existing R185/R186 extraction and failed translator receipts must be reused, not rerun unchanged.

Whole callback chronology, universal joint C1/H1/G witness compatibility (including p0/p2 and adaptive/degenerate prefixes), the complete published-view simulator and shared-oracle probability accounting, coherent pre-beta quotient extraction and optimized-to-source acceptance remain open. End-to-end privacy and soundness are not claimed.
