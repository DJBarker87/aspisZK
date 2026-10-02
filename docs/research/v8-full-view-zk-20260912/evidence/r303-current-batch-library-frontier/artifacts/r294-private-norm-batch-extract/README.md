# R294 private norm batch extraction

This is the lead-selected second extraction attempt for the original frozen batch root. It keeps the same frozen source snapshot, exact root, feature flags, toolchain and optimized cached release command as R293. The only extraction selector change removes broad `core::iter::adapters::chain` and `core::slice::iter` coverage and requests the explicit Chain type/methods plus the specialized Chain `try_fold` and slice iterator `any` bodies. Baseline includes remain `core::option` and `aspis_core::field`.

The purpose is to avoid R293's unrelated unsupported union constant in the broadly included `SliceIter::next_chunk`, while retaining the actual selected traversal and `any`/`try_fold` implementations. No substitution of a `next` loop, source edits, translation, or proof claim is authorized. Extraction `has_errors`, emitted bodies, and any next diagnostics are to be recorded as observed; an LLBC file with `has_errors=true` is not proof input.

R293 remains preserved at `.r21-scratch/r293-private-norm-batch-extract/` and is rejected as proof input: its Charon output had `has_errors=true` because `core::slice::iter::{impl Iterator for Iter<'a,T>}::next_chunk` contains unsupported union constant handling in `core/slice/iter/macros.rs:207:33`, reached through `xs.iter().chain(ys).any(...)` at `r110_norm.rs:62:38`. R293's Charon process exited 0, but this does not override metadata `has_errors`.

The R294 runner records the source hashes, Rust flags, revision basis, isolated 5 GiB high / 7 GiB max / zero-swap / 128-task scope, optimized release extraction, command and full output. Translation is deliberately deferred to lead review.

## Observed extraction result

The R294 Charon command exited 0 and wrote `R294PrivateNormBatch.llbc` (SHA-256 `bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f`) with `has_errors=false`. Root Fun0 is present, local, and has a body. The selected declarations include `core::iter::adapters::chain::Chain` (Type5, Transparent); `Iterator::chain` (Fun3, Transparent body); `Iterator::any` (Fun4, Transparent body); specialized slice iterator `any` (Fun106, Transparent body); specialized `Chain::next` (Fun114, Transparent body); and specialized `Chain::try_fold` (Fun120, Transparent body). The generic `Iterator::try_fold` declaration is Fun58 and remains Foreign/Opaque. The captured census is in `result.json`; the raw LLBC preserves the exact declaration rows and signatures.

GNU time reports Charon exit 0, wall 14.30 s, peak RSS 621520 KiB, swaps 0. The isolated scope was configured at MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. The remote runner checked the same frozen source and Cargo hashes, Rust flags, and source-root input as R293. Full command, log, reservation snapshots, and toolchain are retained. This establishes only the extraction output state; it is not a translation or proof result. Lead review is required before any translation.
