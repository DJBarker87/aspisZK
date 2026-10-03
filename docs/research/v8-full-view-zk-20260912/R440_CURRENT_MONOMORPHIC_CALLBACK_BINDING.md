# R440: current monomorphic callback binding — diagnostic evidence

This checkpoint is diagnostic extraction evidence, not a Lean theorem and not an end-to-end privacy or soundness result. The selected verifier source, its 999,790 / 999,532 CU results, authentication, canonical checks, negative examples, challenge sizes, query counts, and security parameters are preserved. No CU benchmark or unchanged regression was rerun.

## Problem and candidate

R439 successfully translated the generic captured callback, but its focused Lean file failed: the translated backward state did not fit the pinned standard FnMut/FnOnce dictionaries. Every declaration in that failed file remains rejected. R440 tests native monomorphic direct-call resolution instead of introducing a dictionary that discards captured state.

The isolated Charon candidate starts from clean revision `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`. Two source files change. The closure translator retains the compiler-created method binder in monomorphic mode. Before the ordinary transformation pipeline, the driver applies the existing known-implementation resolver to cloned function declarations, then clears only the Fn/FnMut/FnOnce exported method maps required by monomorphic validation. Destructor and other method maps remain intact. The resolver, validators, cached libraries, and verifier source are unchanged. Candidate A and Bv1 were rejected before compilation; their evidence and correction histories are retained.

This changes transformation timing and scope. It is not a general semantics proof for the modified translator. The early pass visits function declarations; globals are not visited by that added pass. The saved R437 inventory records no global FnPtr/FnDef occurrences. Signature FnPtr types and FnDef expression references are distinguished explicitly; regions are retained.

## Focused results

The source-only candidate copy accounts for all 1,169 tracked entries, exactly two reviewed source overlays, and no shared regular source inodes. The optimized direct-driver build uses the 46 pinned cached externs and pinned native inputs rather than a cold Cargo dependency build. It exits 0 in 13.54 seconds, peak RSS 1,569,908 KiB, swaps 0. Candidate driver SHA-256 is `36cd66adb952d877a5ca6e17949fc4685525ed643d1b1fa7e92792d9a1d26625`. The original tool and its build cache were independently checked unchanged by that build.

A new one-call fixture observes updated captured power and uses both mutable and shared captures. Native borrow checking and type checking remain enabled. The original tool capture exits 0 in 0.08 seconds, RSS 116,336 KiB, swaps 0; the candidate capture exits 0 in 0.07 seconds, RSS 115,808 KiB, swaps 0. Its full structural comparison permits only two checked Call.func replacements and separately audited output and declaration/name ordering. It proves no verifier execution claim.

The actual selected `crate::freeze` capture uses exactly the R437 command except the candidate wrapper and fresh destination, with the same frozen source hashes, 16 includes, Rust flags, features, release/offline/locked settings, and compiler. It exits 0 in 13.95 seconds, peak RSS 630,272 KiB, swaps 0, `has_errors=false`. Target `R440ActualMonoClosure.llbc` SHA-256 is `01cd5ddc7086bba5f4e92802f90e59cce4034cf519d495ec35f925b91a6f033d`. Source revision recorded for this capture is `3b9e8d7f0122e6dc966a809904adbd722ae3079d`. All frozen verifier source and original tool pins checked before and after agree.

All NUC jobs use systemd cgroups with MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128 and the reviewed runtime/termination limits. The actual capture's own saved cgroup snapshot reports memory.peak=493,158,400 bytes, swap peak 0, and zero high/max/OOM events. Its terminal systemd summary reports a different peak; both observations are preserved, not silently substituted for the measured GNU-time RSS or saved cgroup snapshot.

## Actual-source comparison boundary

The lead lossless hashcons-expanded comparison finds 16 Call.func replacements. Each maps its original implementation and method slot to the unique existing source-owned method function. Every generic namespace is preserved as the exact original outer implementation arguments followed by method arguments. Every other function field, including statement identity, source spans, regions, operands, destinations, unwind and failure paths, is exact. All type/global/trait/implementation tables are exact, including the actual inner callback Fun112. No source statement, region, error branch, or captured-state field is erased.

The ordered declaration list changes from 264 to 262 nonrecursive groups. Existing Fun71, Fun93 and Fun141 are added; TraitImpl16, 31, 53, 54 and 55 are removed from that list. Those declaration rows remain in the unchanged tables. The group lists therefore do not have equal membership. The independent structural audit agrees on all 16 call references, exact generic arguments and unchanged remaining function fields/tables. Full freeze declaration dependency coverage remains pending; group membership equality is not claimed. The complete literal diff and exact group delta are preserved.

## Focused actual batch translation

The actual freeze directly calls batch Fun29 in six paths. Its complete typed dependency selection contains 62 nonrecursive groups (40 functions, 7 globals, 15 types), including slice fold Fun70 and captured callback Fun112. Only `translated.ordered_decls` changes; every other JSON value is exact, source order is retained, and the pinned typed traversal reports no missing or unclassified references. The source associations remain unchanged. The selection is not a rewrite of pointer or fold semantics.

Target `R440GammaExecutionSelection.llbc` SHA-256 is `96135e91c71f93dcd3aeec7b693eb737e7cf05027456ca973242cf2586088c48`. Focused translation with the pinned R425 Aeneas binary fails with exit 2 in 0.26 seconds, peak RSS 85,536 KiB, swaps 0. It stops before emitting Lean on the actual `TPattern(TRawPtr(QM31, RShared), NotNull)` field from Rust `core/src/ptr/non_null.rs`, at `llbc/TypesAnalysis.ml:485`. Complete output and receipts are retained. No null constraint was erased and no pointer or slice-fold implementation was replaced with an assumption.

## Precise boundary and remaining proposition

No Lean file was compiled in R440. Complete #print axioms output is N/A because these are native extraction and structural diagnostics. R439's failed Lean output is not rehabilitated by this capture.

The first remaining implementation obstruction is faithful support for the actual non-null pointer type and the reachable pointer operations. The first remaining proposition is faithful execution of the actual selected batch callback and slice fold, including captured mutable power, shared gamma, pointer/borrow/frame behavior, arithmetic errors, stopping and returned state, followed by complete callback chronology through rho. Native reference resolution alone does not prove standard-library fold/extend operations or justify a free heap-load function. The existing error-preserving SelectedResearchScheduleProgram must be used; the success-only RelationPrefixCorrespondence exact premise remains unproved.

Full privacy still needs universal joint C1/H1/G compatibility for every legal same-public witness difference, including p0/p2 and adaptive or degenerate prefixes, a simulator for the whole published view with faithful shared-oracle/seed/commitment/retry/stopping/publication behavior, and explicit losses. Soundness still needs coherent pre-beta original quotient extraction, its quadratic-fold connection, the actual shared-oracle challenge law and all losses, and optimized acceptance implying source acceptance. None of those end-to-end gates is claimed here.
