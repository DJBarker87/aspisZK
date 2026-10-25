# S1 original Claims raw-write initialization, 2026-10-25

Status: **native raw-store leaves checked; original Box/caller composition still OPEN**. No enclosing SDK/source premise is removed by this packet. S1/S6 and the <=2^-100 release target remain unestablished. S2 is transferred; the shared finite Claims-to-finish integration on research is not duplicated or modified.

The prior whole-original initialization check stopped at Kani's unsupported union-pointer operation. This packet changes the experiment: begin at fresh raw allocated storage, check the actual monomorphic native row store, and compose the exact original `for p in 0..3` raw store loop. It does not replace the original Box with a supposedly equivalent carrier or attribute this leaf to the complete function.

## Established native claims

The full field source is byte-identical to `25866ec331cc7ce27dd9956609c11d32fa8fa58a:crates/aspis-core/src/field.rs`. QM31/CM31/M31 and Row/Claims retain every native field; all raw u32 values are symbolic, with no canonicality assumption. The two-package workspace retains the 88 frozen source pins. The allocation and deallocation operations are real `alloc::alloc::alloc/dealloc` calls under Kani's normal allocation-success model, not zeroed-storage or decoder/allocator stubs. Allocation-failure and target-runtime correspondence are not claimed.

1. `claims_raw_write::single_row_arbitrary_cell_initializes`: write the complete symbolic `[QM31;29]` into a fresh uninitialized allocation. A subsequent read of an arbitrary one of its 29 QM31 cells passes `-Z uninit-checks` and equals all four expected words. The target also checks Row size464/alignment4, QM31 size16, CM31 size8, M31 size4 and every nested field offset. First/last-cell covers both pass.
2. `claims_raw_write::three_rows_arbitrary_cell_initializes`: the finite three-store schedule on a fresh 1392-byte/alignment4 Claims allocation initializes an arbitrary one of all 87 cells and preserves its exact four words. No initial zero fill is supplied. First/last-cell covers pass.
3. `claims_raw_write::original_raw_loop_arbitrary_cell_initializes`: the ORIGINAL loop bound, row-pointer cast, `.add(p)` and `.write(...)` methods execute on that raw allocation, and the same universal 87-cell initialization/value claim passes. This is the loop skeleton after replacing `out.as_mut_ptr()` with an already allocated raw Claims pointer and `record.decode_k::<29>(p*29)?` with the symbolic corresponding complete row. Those substitutions and the literal frozen loop are recorded in `source-binding.json`. Decoder interleaving, Box pointer projection and Box ownership transfer are not established by this leaf.
4. Negative control `claims_raw_write::raw_missing_write_negative` deliberately omits the store. Kani rejects the native typed read with explicit uninitialized-pointer errors, as well as the subsequent value assertion. The initialization checker is active, and the fresh allocation is not an initialized sentinel substituted by the harness.

The arbitrary-cell formulation covers every cell: all indexes 0..28 / 0..86 are represented by the unconstrained byte modulo29 / modulo87. The layout checks show no omitted word or internal field-padding region on the pinned Apple Silicon target. Neither these checks nor host tool execution establish SBF/ELF layout or release association.

## Exact validation and failed predecessor

Kani0.67.0 official Apple Silicon distribution, rustc `1.93.0-nightly (53732d5e0 2025-11-20)`, all native tool/sysroot and source pre/post pins, optimized compilation and Rust overflow checks, `-Z uninit-checks`, unwind32 and unwinding assertions. No `kani::assume`, stubs, transmute, custom axiom, backend override or initialized allocation replacement. `#print axioms` is inapplicable to native Kani results.

All commands use the one-job atomic local lock and a 180-second/64-process/2GiB sampled aggregate guard. These are ordinary focused Mac jobs, not hard cgroups. No NUC job, scope, extra cap, source adoption or privileged operation was needed here.

| Attempt | Target/result | Exit | Wall s | RSS bytes | Sampled aggregate bytes | Swap |
|---|---|---:|---:|---:|---:|---:|
| v1 | broad symbolic-row pointer/read, codegen | 0 | 0.440342 | 128368640 | 19300352 | 0 |
| v2 | broad symbolic-row pointer/read, watchdog stop | -15 | 3.135870 | unavailable | 2199535616 | unavailable |
| v3 | single row/arbitrary cell, codegen | 0 | 0.227077 | 128335872 | 1638400 | 0 |
| v4 | single row/arbitrary cell, 0/109 failed, 2/2 covers | 0 | 2.243985 | 314654720 | 328744960 | 0 |
| v5 | missing-write negative, codegen | 0 | 0.221674 | 116981760 | 1785856 | 0 |
| v6 | missing-write negative, expected uninitialized-read failure | 1 | 0.451305 | 32571392 | 36847616 | 0 |
| v7 | finite three-store/arbitrary cell, codegen | 0 | 0.450647 | 129777664 | 19841024 | 0 |
| v8 | finite three-store/arbitrary cell, 0/114 failed, 2/2 covers | 0 | 6.051626 | 651821056 | 679641088 | 0 |
| v9 | original raw loop/arbitrary cell, codegen | 0 | 0.439853 | 137134080 | 23904256 | 0 |
| v10 | original raw loop/arbitrary cell, 0/142 failed, 2/2 covers | 0 | 6.073437 | 627752960 | 659030016 | 0 |

v2 received the guard's SIGTERM; it was not accepted partial evidence and was not rerun unchanged at a larger cap. Its symbolic pointer offset across three rows and repeated whole-row reads were replaced by an isolated row and arbitrary-cell check. Only then were finite stores and the original loop added back. All source/tool postchecks passed. Historical source snapshots remain unchanged when later unselected harnesses are appended. Runner owner-label text inherited from an earlier harness was corrected for future runs only; actual historical commands, selected targets and snapshots are retained.

## Checked arithmetic and coverage composition

`S1ClaimsRawWriteRangesV1.lean`, namespace `AspisS1ClaimsRawWriteRanges`, proves:

- For arbitrary initial byte-initialization predicate, induction over n completed 464-byte writes covers every byte below n*464. At n=3 this covers all1392 bytes without an initial initializedness hypothesis.
- The mathematical write-coverage predicate preserves its initial predicate outside the written prefix, and different row intervals are disjoint.
- Every payload byte has unique row/QM31/word/byte coordinates, with domains3/29/4/4.
- Actual source offset domains satisfy p*29<=58, p*29+i<87, row-pointer byte displacement<=928, and every addressed payload byte<1392 and below signed32/unsigned32 maxima. No huge array or recurrence is normalized.

This is explicitly a byte-coverage MODEL. It is not an opaque heap replacement or a native frame/effect law. The native leaves above execute real raw stores and reads; the model supplies arithmetic/induction, while their original Box/decoder/ownership composition remains to be justified.

Focused Lean ranges-v3: exit0, wall2.289058792s, peakRSS2260549632B, swap0; `-j1 -M4400`, one-job atomic lock, exact direct-import/tool pins and warm cache. Seven audits use only standard axioms; outside_frame is axiom-free. Failed v1/v2 elaborations are retained/excluded. They hit recursion while omega inspected the recursive iff induction hypothesis; the successful proof uses explicit Nat order lemmas rather than increased options. No unchanged full replay or new resource overrides.

## Remaining original-source obligations

The raw-loop initialization boundary is now checked for its explicitly allocated/raw/normal-row domain. The entire original Claims initializedness gate remains open because its Box<MaybeUninit<Claims>> pointer projection and ownership transfer, actual fallible heap allocator, decoder interleaving/error paths and target/runtime installation have not been composed with this result. The prior source inspection shows that MaybeUninit::as_mut_ptr is already a direct pointer cast; rewriting it to the same cast or rerunning the unsupported whole check is not a new route. A genuinely supported compositional wrapper/footprint proof, or a fully validated and explicitly adopted source route, is still needed.

Existing complete native Claims decoder/control and safe/frozen normal-return/allocator-request comparisons are reused only at their published scopes. The safe-storage candidate remains NOT ADOPTED. No production Rust, verifier artifacts, CU bounds or other session's worktree changed. The shared source/caller/kernel/release joins remain with their owners.

Read-only packet check: `python3 tools/s1-claims-raw-write-20261025/check.py`. Source-only `focused-extractor-proof-packet-v1`; no binaries/LLBC/GOTO files. No compiler or host call occurs in the checker.
