# Lead review: follow-up checkpoint ba8cc28e8 (2026-10-16)

Merged onto 5b8d999db as a merge commit, not a fast-forward, because the live
session had advanced. The only paths both sides touched are the 28 files of
506224f37 (concrete literal per-attempt budget), which the worker rebased
across. The lead checked all 28 and they are byte-identical on both sides.

## Amendment to Decision 1 (ca137f5db): begin unroll accepted

The pinned extractor rejected the early-return `for` loop over `zc` in
`r1_wire::begin`. The user approved the refactor. The lead read the diff
against 99263bea0: ten straight-line `semantic_validated(validated_record(3..12)?)?`
calls in the original order, and no other change to the file. Gates passed
at 63990fffe:
- 1,233 codec outputs byte-identical;
- 583-call counter trace identical (349/234);
- all 23 checkpoint tests;
- failure injection at each of rows 3..12 gives identical errors, event
  order and state prefix.

It is part of the J1.R13 candidate source. CU is reported at J1.R13.

## Decision 1b: Prepared helper patch approved, same terms

`tools/verify-prepared-prefix-kit/proposal-prepared-helper-fields/proposal.patch`
was read by the lead.
- It returns `(alpha, row)` from the existing branch.
- It moves the claim aggregation into `prepared_claim`, a helper taking
  y1/inactive as field arguments.
- The draw order (gamma 27, kappa 28, alpha0 29, alpha1 30, then queries and
  rho) is unchanged, and the aggregation still runs after rho, with the same
  `trace::value` calls in the same order.
- The `row` selection changes from `folds()==1 → 30 else 31` to
  `folds()==2 → 31 else 30`. These agree because `Variant::folds` returns
  only 1 or 2 (`transport.rs:8`).

It is approved for the J1.R13 candidate under the same gates as begin:
- codec 1,233 identical;
- counter trace identical;
- 23 checkpoint tests;
- an injection check that fails the `EbyKDot::push` and query paths for each
  variant (S1 and two-fold) and gets identical errors and trace values.

The generated emission must compile, and its theorems are accepted only
with `#print axioms`. Any further verify-path source change needs a new
lead decision. Workers should report the blocker and a proposal before
patching, as was done here.

## Accepted, unconditionally

- Worker B: `readonly_buffer_meta_ok`, its exact-result, success-iff and
  InvalidAccountData-iff proofs, and the single extended
  R16ReadonlyMetadataProjection premise. The harness (7 stage1 + 8 stage2
  mutations/controls) runs on the J1.R13 artifact.
- Worker C: helper success supplies `hs`; the decoded lane transition is
  fixed; the emitted first caller body derives `hd` and supplied-public
  equality for both variants. The tx1/mark/error boundaries remain universal
  parameters. It does not yet show that the actual tx1 body reaches the helper.
- Worker A: begin derives all 15 calls with state/row carry, plus the opening
  new/absorb/block equations; BeginProvenance and PrefixAdapter derive
  strict full25 decoding from actual Prefix success.
- Re-pin inventory: 268 unchanged, 21 re-extracted, 1 authorized
  replacement, and 0 unresolved within the registered cones. The lead
  reviews it against the final release cone at J1.R13. Inventory review is
  a release gate, not a proof gate.

## Noted, not accepted as evidence

- The process deviation is recorded: one B launch overlapped a lead Lean
  job. Launch gating must suppress on preflight failure.
- The overwritten pre-unroll LLBC blob. No theorem depends on it.

## Open (unchanged list, items 6–7 of the 2026-10-16 list)

- Actual verify rows 15..24 and opening rows 25..32, including the row-26
  reseed reachability and the whole carry.
- Equality of the completed transcript bytes to the full25 parsed records.
- `semChalsZ_read.hread` and htyped/ha.
- The source construction of C2Word.literalMessage, which is custody
  data and cannot be recovered from the root.
- Showing that tx1's body reaches the helper.
