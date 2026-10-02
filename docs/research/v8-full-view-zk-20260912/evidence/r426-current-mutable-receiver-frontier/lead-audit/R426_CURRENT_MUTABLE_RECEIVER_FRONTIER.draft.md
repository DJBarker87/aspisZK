# R426: actual mutable receiver frontier

## Boundary

This milestone records a focused compiler/frontend diagnostic for the selected batch-inverse validation path. It proves no Lean theorem, callback execution correspondence, privacy, or soundness result. No verifier Rust or security parameter changed; the saved 999,790 / 999,532 CU results remain the campaign results, with no benchmark rerun.

The pinned Charon command completed once with exit 0, 14.45 s wall time, peak RSS 625,372 KiB and 0 swaps. The systemd scopes retained MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0 and TasksMax=128. Source revision: 3f25c2f0287fc6244591c8aa29463f808902feb3. The exact command, seven selected source checksums before/after, pinned toolchain, resource receipts, stdout and stderr are retained. `#print axioms`: not applicable; no Lean target was generated or compiled.

The sole new print switch was `--print-original-ullbc`, plus a fresh destination. This captures Charon's representation after MIR translation and before its cleanup passes. It is not a rustc MIR dump. The recorded output SHA-256 is 203ba64981a75e9348e96bdf2920f1905f42c6d756de3c644e60006a440ab412. Its try_fold loop already calls `next(copy self)` (stdout line 2498).

The initial full serialized comparison gate failed and its launcher exited 1. That result is preserved. Lead inspection of the saved files found only the two intended operational-option differences and a permutation of the 347 short-name map entries. All function/type/global/trait declarations, item names, files, declaration ordering, target information and other serialized fields were exactly equal. Pinned native source identifies short_names as an IndexMap keyed by ItemId. Its serializer emits key/value records in insertion order, its lookup uses the key, and compute_short_names inserts candidates while iterating a std HashMap. The saved table has 347 unique keys in both captures with exactly equal values; 167 record positions differ. The audit treats only this field as a keyed map. It does not sort other lists, remove identifiers, erase bodies, or claim general compiler equivalence. The pre-launch README/manifest remain historical snapshots and are not the current execution result.

## Actual source path

The selected batch checks empty or zero inputs and can return Error::Domain. Its source calls `xs.iter().chain(ys).any(...)`. The saved R396 generic AST contains the default Iterator::try_fold body; the saved same-source R327 monomorphized AST records the two component try_fold instances through Chain::try_fold. These are recorded AST/source facts, not source-execution theorems.

The R425 failure's displayed span at iterator.rs:78 refers to the Iterator::next trait declaration. The actual rejected receiver operand is Copy(Local 1) in Iterator::try_fold at iterator.rs:2493:28–39; self has a mutable-reference type and remains an input local used at the loop call. The source loop uses self.next(). Replacing the copy with a move would consume the receiver in Aeneas and is not justified. Removing mutable-borrow rejection is also not justified.

Pinned Charon retrieves optimized MIR for nonlocal standard-library functions even with `--mir built`; that option selects built MIR only for local definitions. Pinned Rustc allows non-Copy types in Copy operands after drop elaboration and has distinct CopyForDeref and reference-simplification transformations. The saved ULLBC does not establish which transformation produced this receiver operand.

## First remaining proposition

Establish the exact imported MIR receiver/retag semantics and a faithful source-bound execution bridge for the selected try_fold, preserving receiver reuse, all iterations, stopping, ownership and errors. Any frontend repair needs that justification and focused checks. Full callback chronology, freeze execution, the whole published-view simulator and the soundness extraction/acceptance arguments remain open.
