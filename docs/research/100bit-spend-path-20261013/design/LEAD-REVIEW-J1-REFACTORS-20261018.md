# Lead review: verifier refactors merged after deb68369b (2026-10-18)

Production commits reviewed (all merged through the worker/integration
merges, without a lead checkpoint report):
- d4da2a662: Decisions 1d (`verify_finish`) and 1e (the eight-pair
  `queries` unroll);
- abd4c40a4: the fixed-22 query trace unroll (1f item 2);
- 8c348ebbe, 2a5b09f40, db4b01bca, d0dbb2181, 4c7eedea7 and 88b9bd4f1:
  the semantic rounds unrolled and moved into owned helpers, with tuple
  assignment (1f items 1, 2 and 4).

## Shape: conforms

The lead read the full diffs of `transcript.rs` and `r1_semantic.rs` against
deb68369b:
- the eight hash pairs and the 22 trace calls are in the original order
  over a fixed `[u32; 22]`;
- the semantic round body is unchanged, with `semantic_boundary` and
  `semantic_value` as moved expressions;
- ten rounds are written out with constant indices.

No arithmetic, type, error, call-order or public-signature change was seen.
One harmless leftover: a `#[cfg(feature = "prover")]` block referring to
`round_checks` remains inside the `cfg(not(feature = "prover"))` copy of
`semantic_round`, where it is compiled out.

## Gaps that block acceptance

1. **The two `cfg` copies.** `semantic_round` and `semantic_rounds` now
   exist twice, once for `feature = "prover"` and once for
   `not(feature = "prover")`. The deployed verifier uses the
   `not(prover)` copy. The native codec and saved-proof gates build the
   prover (the prover binaries require `prover`), so they may never execute
   the verifier copy. Required:
   - native evidence that the 1,233-case codec and the 583-call ordered
     trace pass with a build using the `not(prover)` verifier path, or a
     differential showing the two copies produce identical results and
     trace;
   - preferably, merge the two copies back into one body with a
     `cfg`-gated extra output, so they cannot drift.
2. **SBF stack and CU predate these changes.** The passing stack audit and
   CU replay (8089cab8f, 2026-10-17 05:48) come before all of these
   commits (11:15–11:43). The new helpers change the stack frames of
   `verify_finish`, `semantic_rounds` and `semantic_round`, and the unrolls
   change code size. Required: one SBF build of the current tip with the
   release features (`pool-adapter,private-leaf-salts`), a stack-warning
   audit (no frame over 4,096), and a stage1/stage2 CU replay on the saved
   fixtures, compared with 1,342,725 / 1,226,423.
3. **No checkpoint report.** Decision 1f requires every refactor to be
   listed in the next checkpoint report with its gate evidence (codec,
   ordered counter, 23 checkpoint tests, injections at every moved failure
   point, reverse-patch audit). Required: that report, before these
   refactors count as accepted release source.

## Standing gate amendment (applies to Decision 1 and every later source change)

Every production verifier-source change now also needs:
- an SBF build with the release features;
- a stack audit, because the begin unroll's 8-byte overflow (fixed in
  8089cab8f) was invisible to native gates;
- a CU delta.

This can be batched once per checkpoint. A source change without it stays
a candidate.
