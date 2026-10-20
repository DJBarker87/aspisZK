# Powers replacement: proved candidate for the S1 extraction gap

Status: PROVED replacement arithmetic; measured six-fixture and strict-stack PASS; NOT ADOPTED. Production freeze b2727acd3 is unchanged.

The frozen `powers` helper uses `core::array::from_fn` with a borrowed mutable callback. Its callback arithmetic is already proved, but the recorded Charon/Aeneas library-lowering problems prevent closing the whole helper through that route. A small safe explicit loop avoids that dependency. Its first two initializers were proved but exceeded one existing per-fixture settlement allowance; those failures remain recorded.

The selected successor writes the current power, increments the cursor, and returns immediately after writing the last entry. It skips the final multiplication whose result is unused. Exact proposed Rust diff, selected raw extraction, two focused Lean proofs, import/source/object pins and runtime receipts are in:

`../lean-candidates/s1-early-return-powers-proved-candidate-20261020/`

The theorem `early_powers_total_exact` proves, for every machine-size array length N and canonical input x, successful termination and canonical outputs with decoded entry j equal to x^j. It covers N=0, checked indexing/writeback, cursor overflow-freedom, early return, each continuing multiplication and symbolic loop progress. It reuses the already proved full current field arithmetic, without free operation-law or loop-success premises. Its four printed axiom reports are standard-only. The source checker confirms exact emitted function bodies after a reversible name prefix, matching carrier types/constants and nine frozen source cuts. Extraction-tool correctness and SBF machine semantics are not proved by this checker.

Candidate ELF: `c9926274dcc16eab6d09d91f39af5e38ee6149cfb6dceb76ff6c666846e5a648`, 1,506,440 bytes. Six cached fixture replays preserve checkpoint-tail and settlement-return hashes and pass strict stack audit. Stage 1 saves 2,986–3,006 CU and settlement saves 5,191–5,215 CU against the current frozen build. All six pass PREREG-PROOF-SIZE-2 item 1. Maximum measured stage 1 is 1,196,295 CU; maximum measured settlement is 1,173,563 CU. Native optimized old/new tests also pass 268 full-field samples at eight lengths, including actual parent sizes 4 and 7. Neither set of tests establishes universal old/new equivalence or a universal CU bound.

Before accepting this as frozen S1: adopt the concrete patch through the lead's source-freeze process; run the remaining standing runtime/prover gates and regenerate the universal CU bound; pin the new source and ELF; extract/re-pin affected parents; connect actual Prepared inputs and calls to this owner. A whole-library formal equivalence with the old `from_fn` helper is not claimed. The replacement has its own whole-helper theorem.

Independent current-source progress is committed in c707514a5: emitted S2 row/inactive composition and optimized table-cell correspondence. Actual grouped accumulation and outer caller refinement remain open. The overall 100-bit soundness goal remains active; this report closes no unproved global cryptographic or runtime assumption.
