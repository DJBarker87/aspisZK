# Lead note on the R1 soundness gap map (2026-10-19)

Accepted: `R1-SOUNDNESS-GAP-MAP-20261019.md` (worker branch
codex/r1-soundness-gapmap-20261019, eight commits, read-only). Spot checks:
`checked_acceptance_failure_bound_no_model` is at
`lean/RawChecksAdaptiveFailureNoModel.lean:34` with the hypotheses `hQ`,
`htag`, `hchecks`, `hN` as listed; `tx2_authenticated`, `resume` and
`finish_relation` exist in `crates/aspis-r1-cost-probe/src/verifier.rs`
(lines 450, 379, 332) and have no mention in `lean/` or `lean-candidates/`.

## Reading

Of 52 links to the target theorem (T): 14 proved, 1 proved-stale, 10 re-pins
owed (the ten kept CU candidates and the whole-cone inventory), 4 refinements
owed, 15 open, 8 premises. The Lean model of the protocol is essentially
complete (M1–M9); the gap is the source side. The largest single open item is
stage 2: `tx2_authenticated`, `resume`, the 12-query loop and
`finish_relation` have no extraction and no owner. The closest composed
theorem bounds model-acceptance-without-extraction by 12Q²/2^256 +
N·15/2^109 + 2^-126 for a free decoder, decision and prover; nothing ties it
to the deployed transactions yet.

## Decisions

1. **Step 0 (freeze the verifier source) is now tied to the proof-size
   test** (`PREREG-PROOF-SIZE-20261019.md`). If the candidate format is
   viable, the freeze is taken on the new format, not the current one, so
   the re-pins (S1–S10), the stage-2 extraction (R14), Merkle acceptance
   (R13) and the commitment words (R12) are done once. The commitment-layer
   items the format change touches are open today, so changing the format
   first repeats no proved work. If the format is not viable, step 0 is
   taken on the current source and the critical path runs as written.
2. The three source candidates on the R3 row (heap overwrite helper,
   accumulator zero-initialisation, composition array copy) are not adopted
   until step 0; their adoption is a user decision at that point.
3. The ROM, Aeneas-correctness and toolchain premises are to be re-accepted
   in an R1 note (they are dated 2026-08-25 for V5 in
   `docs/assumptions-ledger.md`); to be written at step 9.
4. `verifier.rs`'s admission hash in `FINAL-SOURCE-ADMISSION.json` is stale
   by the prover-only error variants (`.text` identical, LEAD-REVIEW-
   CU-BOUND-2); re-pin at step 1.
5. Statement binding is proved for withdrawals only; transfer joins at step
   8.

Unverified by the worker, carried as open: host receipts for
`ConcreteBinding`, `LiteralClassifier`, `SpendRelation`,
`LiteralAcceptanceTerminal` (status rests on the lead reviews); the extracted
sources behind the proved source rows were not diffed against current
production Rust; the root checkout's uncommitted `current-merkle-source-
execution` evidence is not counted.
