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

## Addendum (2026-10-20): M10 composed, conditional

Codex job cx-m10 (commits d1281b25f, f7c7392a8) landed.
`RawExtractorCostComposedV2.recorded_extractor_cost_and_failure`
(`lean/RawExtractorCostComposedV2.lean:124`) bounds the accepted-run expected
field, hash-log and bit cost of the recorded-run extractor by an explicit
polynomial and carries the exact M9 failure bound with δE = 2^-126 ≤ 2^-120.
Four targets compiled locally (exit 0, ≤ 2.23 GiB, standard axioms;
receipts in `evidence/extractor-cost-composed-20261019/`). Status of row
M10: PROVED (conditional). Named implementation hypotheses still to
discharge: output refinement, bounded arithmetic jobs, implementation
overhead, log-read accounting, bit accounting, uniform overhead
constants/degree. These join the source-side list (step 9 inputs).

## Addendum (2026-10-20): R22 partial

Codex job r1-overflow-free (a85e60cd0 after WIP 93f5025d9, 9d906cec2) landed:
`design/OVERFLOW-FREEDOM-INVENTORY-20261019.md` and
`evidence/overflow-freedom-20261019/` (36 focused targets, 50 theorem reports,
standard axioms, ≤ 3.00 GiB). Proved: decoder value/loop totality, ρ
push/value totality, control and index bounds, the field/semantic-loop/
parser/folded-dot range proofs. No admitted-input overflow was found.
R22 stays OPEN: the pinned stage-1 extractions predate the CU optimisations
(weights, private pairing, fast dots have no extracted bodies yet), so their
overflow proofs wait for the S1–S9 re-pins; then round/prepare composition,
the outer decoder guards, the global ρ caller invariants and the
deployed-to-checked bridge. Sequence: S1–S9 → R22 (stage 1) → R22 (stage 2,
after R14).

## Addendum (2026-10-20): binary commitment model landed

Codex job r1-commit-model (5e3d9b2c4 after 61e1a7928, d217103e1): 25 `Bin*`
modules (`design/BIN-COMMITMENT-MODEL-20261019.md` maps each to the
eight-way theorem it replaces), 106 theorems, standard axioms, ≤ 3.03 GiB,
receipts in `evidence/bin-commitment-model-20261019/`. Proved at the model
level for the binary format: node/leaf grammar, multiproof ⇒ per-query path
acceptance with dedup preservation and padding isolation, opening binding
with collision targets counted as 6·Q²/256³² (the κ input), causal word
recovery and compiled-run word stability. Rows M7, M8 and R11's model half
are PROVED for the binary format; their eight-way versions stay as history.
Obstruction (same as D77.2): unconditional disjointness of node preimages
from arbitrary public-byte hashes is false (`verifier.rs:382` hashes public
bytes verbatim); separation is proved under a length premise, to be
discharged from the fixed public-statement length in R-wire. Source side
(R12, R13, R14) continues in the stage-2 extraction.
