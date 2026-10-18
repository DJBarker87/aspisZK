# Lead review: verify/query/C2 follow-up checkpoint 6dd9028e9 (2026-10-18)

The checkpoint is merged as a merge commit. Its base is 503d9b968, and the
branch had advanced. No path is touched by both sides. Production files are
byte-identical to the branch tip: the worker-side a555c8526 matches the
branch's 88b9bd4f1 source, and this merge adds proofs and evidence only.

## Against the 1fc20c436 requirements

3. **Checkpoint report: met.** The note lists every 1d/1e/1f step, the
   extractor blocker behind it, and a forward/reverse patch audit that
   covers both cfg alternatives. Final-source gates passed:
   - codec 1,233;
   - 583 ordered calls (349/234);
   - 23 checkpoint tests;
   - verify injections: 112 cases at 55 fault points, under both observers;
   - query injections: 102 cases at 16 digest positions plus the decoder.
1. **`not(prover)` coverage: partly met.** The 23 checkpoint tests and the
   saved-S2 verify runs exercise the verifier through tx1/tx2, but the
   report does not state the Cargo feature set of each gate. Still required:
   one line per gate giving its exact `--features`, showing that at least
   the 23 checkpoint tests and the verify injection runs build without
   `prover`. The preference for folding the two cfg copies into one body
   stands. It is not a blocker if the coverage line is supplied.
2. **SBF stack and CU after the refactors: OPEN.** No SBF build ran. Until it
   does, the post-refactor source stays a candidate (standing gate,
   1fc20c436).

## Proofs accepted

- Rows 15–24 come from actual helper success: the exact returned α order,
  unchanged hash, and transcript state carry. Six standard-only axiom
  reports.
- `verify_finish` composition: three targets, 19 standard-only reports. The
  first model was correctly rejected because its axioms audit inherited
  `core.fmt.Formatter` through `try_into().unwrap()`. The final model
  exposes that callee as an explicit API, and no root-conversion
  implementation theorem is claimed.
- Same-table `hread`/`ha`/`htyped`. `htyped` keeps an explicit no-hit
  premise.

## Still open

- C2 execution, blocked by Aeneas.
- Whole-trace embedding.
- Literal custody.
- The eight explicit arithmetic/allocation/circle/root-conversion API
  boundaries in the finish model.
- The `not(prover)` feature line and the SBF stack/CU run above.

## Addendum: re-cut 63cd5be53 (2026-10-18)

- **Packaging: passed.** All 18 commit trees have every file at or under
  90 MB, and the oversized blob is absent. Fast-forward.
- **`not(prover)` coverage (item 1): met.** The 23 accepted checkpoint tests
  build without `prover`, and so do 112 + 112 verify cases, 102 query cases
  and the identical 583-call trace. Exact features are recorded in
  `evidence/checkpoint-recut-20261018/checkpoint-report.json`.
- **SBF stack/CU (item 2): FAILED.** The ELF built from revision 234a1431b
  has a `verifier::tx1` frame of 4,672 bytes against a 4,096-byte limit.
  `tx1_finish` (Decision 1c) has no surviving call boundary: it was inlined
  back into `tx1`. All three current stage1 replays fail with a stack access
  violation, and stage2 is never reached. **The current candidate source does
  not run on SBF.** There is no valid CU delta.

## Decision 1g: `#[inline(never)]` on `tx1_finish`

This is the same remedy that fixed `begin` (8089cab8f): keep the split frame
by forbidding inlining. Only the attribute changes. Gates:
1. The strict stack audit shows no oversized frame on any function reachable
   from the admitted entrypoints (stage1 `[3,10]`, stage2 ASQ8). Oversized
   frames on unreachable symbols are listed and justified.
2. The stage1 and stage2 replays pass on the saved transfer and withdrawal
   fixtures, with the CU delta reported against 1,342,725 / 1,226,423.
3. Codec, ordered trace and the 23 checkpoint tests are rerun if the
   attribute changes anything native. It should not.

If `tx1` alone still exceeds 4,096 bytes, `#[inline(never)]` may also go on
the semantic-round helpers (`semantic_rounds`/`verify_finish`) under this
decision. Any other remedy needs a new decision.

**Until Decision 1g passes, the branch tip's production source is not
runnable on SBF.** All CU and runtime claims refer to 8089cab8f-era
artifacts.
