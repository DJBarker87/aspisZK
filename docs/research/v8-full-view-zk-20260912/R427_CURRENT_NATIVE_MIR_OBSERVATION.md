# R427: native imported MIR observation

## Boundary

This milestone records a finite compiler diagnostic, not a Lean theorem or a privacy or soundness proof. The selected verifier source, negative examples, authentication, canonical checks, challenge sizes, query counts and security parameters were not changed. The saved 999,790 / 999,532 CU results remain unchanged; no benchmark or unchanged regression was rerun.

The isolated observer only reads the selected foreign `Iterator::try_fold` body and prints native Debug plus explicit statement/terminator source information, assignment Use retag flags and call argument operands/spans. It returns the same cloned body. This output is not a complete field-by-field serialization of Rustc Body, and the finite AST comparison is not a general compiler-equivalence theorem.

## Verified diagnostic

The pinned Charon source revision is `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`; Rustc is nightly-2026-06-01, commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. The final hook checksum is `1013364396ff23f0ce80fcd31561ef0018126c01f445cbbd85fc5d95bc66322f`; the compiled driver checksum is `3fe3b14ca29616e291684199b3977b4ac341405e8c5739c4b0a467bf81ed1ba0`. It compiled with exit 0 in 12.44 s, peak RSS 1,610,060 KiB, 0 swaps, using 46 exactly pinned cached dependencies. Every tracked source and cached dependency checksum was stable during compilation. The original Charon source, cache and binaries were retained unchanged. This explicit optimized Rustc command is not claimed to reconstruct the historical Cargo invocation.

The actual selected batch extraction completed with exit 0 in 14.17 s, peak RSS 630,268 KiB, 0 swaps. The final LLBC checksum is `e2295d8c7d4b45d9f3b20b4cfaff03d7272398396d579294b06b1ea1224679a9`. Target: `crate::circle_norm::joined_inverse::line_norm::r110_norm::batch`, frozen source snapshot revision `13617a70553ed3c43cee312acba2407b29a7052d`, campaign launch revision `a6cdbfac929ee3afe75b42382f08370216664145`. Seven selected source checksums and the complete R396 baseline checksum are pinned before and after the job. The entire saved R396 extraction plan is pinned before launch, including root, includes and Rust flags.

Both jobs used systemd with MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0 and TasksMax=128; actual cgroup receipts include peak memory, swap and OOM counters. Exact commands, sources, exit statuses, GNU time logs and hashes are saved. `#print axioms`: not applicable; no Lean target was generated or compiled.

The complete decoded LLBC matches the R396 baseline after changing only the exact destination path and reordering the 347 unique short-name key/value entries as a map. Every other field, declaration, body, type, identifier, list and literal is exactly equal. No general list sorting or identifier/region erasure is allowed.

## Observed receiver

The final frame identifies the canonical definition as `core::iter::traits::iterator::Iterator::try_fold` and records Rustc's user-facing display as `std::iter::Iterator::try_fold`. The original selector matched the canonical string against user-facing formatting, producing no frame. The corrected selector scopes the native no-trimming/no-visible-reexport formatting guards to the name query.

The imported body is `Runtime(Optimized)`. Its local `_1` has type `&'{erased} mut Self/#0`. Basic block bb1 already calls `_5 = <Self as std::iter::Iterator>::next(copy _1)`, returning to bb2 and unwinding to bb16. The explicit argument marker records `copy _1` at iterator.rs:2493:29–33; its terminator covers 2493:29–40. The body also preserves the loop backedge, continuation, residual, return and cleanup branches. These are observed native MIR facts, not an ownership or execution correspondence theorem.

The frame contains one begin/end pair, 40 statement-source records, 11 assignment Use retag records, 17 terminator-source records and 6 call-argument records. No explicit assignment Use retag precedes the bb1 receiver call in that block. That does not establish the absence of implicit call/entry retagging or justify replacing Copy with Move. The diagnostic pins the receiver Copy before Charon translation; it does not identify the exact Rustc optimization ancestry of that operand.

## Preserved failures

All failed preflights and launches remain in the evidence: the initial clone's incorrect symlink assertion, the stale build assertion, the stopped Cargo dependency rebuild, the local toolchain-field assertion, and the first remote launcher failure before extraction. Attempt B completed extraction in 14.51 s with 629,764 KiB peak RSS and 0 swaps, with matching full LLBC but zero frame markers; its audit exit 2 is retained. The first diagnostic driver compiled successfully in 14.34 s with 1,598,256 KiB peak RSS and 0 swaps, and its source/receipt/output pins are retained. None of these historical results was rewritten as a success.

## First remaining proposition

Prove a source-faithful execution treatment of the selected mutable receiver call that preserves receiver reuse, mutation, all iterations, stopping, errors and ownership. Copy-to-Move replacement and removing mutable-borrow rejection remain unjustified. Pinned Rustc's reference simplification code is retained as source evidence only; the observed body does not prove its transformation history or a valid inverse lowering.

Then close the actual freeze and full callback chronology through circles, gamma, kappa, tau, alpha, q22 and rho, using the existing failure-preserving schedule. The universal joint C1/H1/G compatibility, whole published-view simulator with shared-oracle/retry/publication behavior and explicit losses, coherent quotient extraction before beta, and optimized-to-source acceptance remain open. End-to-end privacy and security are not claimed.

## Evidence

The complete bundle is [evidence/r427-current-native-mir-observation](evidence/r427-current-native-mir-observation/). Final build receipts are in `lead-direct-launch-b/direct-audit-b/` and `lead-audit/reviewed-direct-build-receipt-b.json`; final capture receipts and native frame are in `launch-gated-runner-attempt-c/saved-output/`. Earlier notes, plans and nested checksum indexes are historical snapshots; the bundle's root checksum index and copy manifest describe the published files.
