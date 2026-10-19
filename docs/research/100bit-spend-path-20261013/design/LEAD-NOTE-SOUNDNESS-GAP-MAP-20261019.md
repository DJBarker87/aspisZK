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

## Addendum (2026-10-19, late): integer-overflow semantics as a gap-map row

Aeneas translates Rust integer operations with checked semantics: an overflow
is a failure of the translated function. Rust release builds wrap unless
`overflow-checks = true`. The two extracted prover-side crates
(`aspis-r1-cert-check`, `aspis-r1-cert-build`) have overflow checks on in
release (root `Cargo.toml`, D73), so the compiled checker is the modelled
function. The SBF programs (`programs/r1-cost-probe`, `programs/aspis-pool`)
have no overflow setting and are built wrapping.

For (T) the needed direction is "deployed accepts ⇒ model accepts". If the
deployed verifier wraps at any operation where the model fails, that
direction is not established. New row **R22 (OPEN)**, owner lead/Codex:
one of (a) a Lean proof that no operation in the stage-1 and stage-2
extraction cones can overflow for any input (per-operation range lemmas;
the builder work already has "u64 reductions mod p never overflow",
LOG:6076); (b) an SBF build with `overflow-checks = true` for the verifier
program, re-measured against the stage-1 CU margin (16k); or (c) an audit
that every arithmetic site on the admitted routes uses explicit
`wrapping_*`/`checked_*` operations (23 in `fast_pairing.rs`, 10 in the
adapter today), with the model matching by construction. R22 is on the
critical path before step 9 (C3). Size: M for (a), S for (b) and (c).

Prover side: measure how much of the 35.8 s P_R1 check is the overflow
checks before deciding between a no-overflow proof and keeping them on.
