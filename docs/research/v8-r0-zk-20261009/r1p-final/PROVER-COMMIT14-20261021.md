# Prover commitment continuation 14 — 2026-10-21

Branch `codex/cx-prover-commit14-20261021`, base `3bbbd12bb`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit14-20261021/`.

The actual release target is not yet established. This report is updated by stage.

## Stage 1: owned indexed material schedule

The proof-only reference adds `material_columns_owned`, `collect_qm31_owned`
and `material_padding_owned`. Fresh owned vectors and expander state cross
recursive calls. Columns retain their initial vectors, append exactly 1024
scalar results, then balance before the next column. Padding skips active
and dependent rows; errors retain the state and partially written values.
The caller must supply initial empty columns, correct remaining count and
valid dependent/layout indices. No production body or Cargo input is edited.

Charon/Aeneas v1 both pass (23.684/0.622 s, 681368/92576 KiB, zero swaps).
V2 makes the column count explicitly decreasing so the finite induction
requires no hidden length-preservation premise. Charon/Aeneas v2 both pass
(23.893/0.658 s, 673080/92576 KiB, zero swaps). All field operations are
translated concrete bodies, not opaque summaries; no external template is
introduced. Types receives the same explicit discriminant port as part 9.
Generated Funs is adopted verbatim. Original generated text and tool hashes
are retained in extraction evidence.

`ProverCommitMaterialRecursion.extracted_finite`, `qm_extracted_finite`,
`columns_extracted_finite`, and `padding_extracted_finite` identify each
whole extracted recursion with its symbolic finite schedule, preserving
allocation/indexing/scalar/balancing failures. Padding requires
`row.val + n = 1024`; columns require `remaining.val = n`. These are
reference theorems, not a source-to-model execution join.

J8373 Types and J8374 Funs pass. J8375 checks both scalar collectors.
J8376/8377 are excluded column-induction elaboration drafts; J8378 checks
columns; J8379 checks all six final theorem audits, exit 0, wall 2.05 s,
peak RSS 2596212 KiB, zero swaps. All accepted printed axioms are a subset
of `[propext, Classical.choice, Quot.sound]`. Exact modules, source hashes,
dependency fingerprints, revisions, errors and full audits are in the Lean
JSONL and verbatim logs. No failed draft is adopted as proof evidence.

The Kani one-iteration comparison is in progress at this stage commit.
The material schedule has not yet been identified with the entire shipped
builder or canonical raw-array projection. No endpoint premise is removed.

## Stage 2: retained global oracle and observer boundary

`ProverCommitMaterialSupport` proves deterministic support through the whole
indexed material-column and padding reference: if two retained callbacks
agree on every domain/seed/counter expander frame, all returned values,
errors and states agree. The hash is never reset between calls, rows or
columns. Scalar rejection, tower coordinate order, collector, column and
padding induction are all included. This is stronger than per-call local
support but remains a deterministic reference result. It neither proves
fresh independent answers nor instantiates the shipped global-window join.

J8382 is an excluded simp-loop draft, fixed by unfolding only the symbolic
zero branch once; no recursion-depth cap is raised. J8383 passes the focused
support lemmas; J8384 adds the whole extracted indexed-column and padding
consumers and passes: exit 0, wall 2.01 s, peak RSS 2587472 KiB, zero swaps.
All fifteen printed audits use only the standard three axioms. The column
result needs only `SameFrames`; padding also states `row.val ≤ 1024`.
These are oracle-support conditions, not a replacement for either headline
execution premise, and do not hide a whole-execution equality.

`ProverCommitObserverBoundary.replacement_changes_history` proves for every
oracle, every existing history and positive query fuel that `.done` and
one query yield different complete histories. `no_unrestricted_history_transport`
then rules out universal suffix-history equality under an arbitrary program
replacement. J8380 is an excluded reserved-token syntax draft; J8381 passes
both audits with `[propext, Quot.sound]`: exit 0, 1.70 s, 3503196 KiB, zero swaps.

This directly tests the endpoint handoff: `RomObserverBin.observerMap`
preserves `source.observe adv` but replaces its query program with the
independently quantified `observer_program adv`. `GamesR1PBin.realGameP`
uses that program on both the rejection and successful-output branches.
The suffix counterexample is an obstruction to inferring complete history
equality for an unrestricted handoff; it is not a counterexample to the
actual privacy bound or to a correctly identified source program. Supplying
the actual program and proving its operational correspondence remains work.
A reflexive coupling of the mathematical constructor would not establish
that the shipped builder/checker/retry execution runs that constructor.

The all-family ledger is retained in `callback-coverage.json`; material
reference support is added without promoting it to shipped callback-log
coverage. Packing, D collection, successful source-seed wrapper disposal,
salts/tree traversal, retries, aborts and callback-history identification
still need actual source joins. Existing local callback checks cannot supply
these by name alone. No peer-owned source-identification, runtime-join or
final-release module is edited.

## Stage 3: global-window bridge into the new extraction

`ProverCommitMaterialWindow` explicitly transports the new extraction's
state to the existing global cursor/cache carrier. Roundtrips and
`next_bridge` preserve success, fail and divergence. `finite_window` proves
that a local scalar-prefix backend may replace the retained global backend
only when their answers agree on refill positions in its symbolic window.
`scalar_window` specializes to all sixteen rejection attempts, including
exhaustion, at the current mapped cursor. No new oracle reset, independence
claim, or probability assumption is introduced. This supplies the window
bridge for the new material extraction; it is not the full real execution join.

J8385 is an excluded argument/elaboration draft. J8386 checks the carrier
and finite-window bridge. J8387 adds `scalar_window`, exit 0, wall 2.19 s,
peak RSS 4051652 KiB, zero swaps; all seven printed audits use only standard
axioms. `ProverCommitMaterialIteration` states exact one-iteration equations
for both collectors, with arbitrary vector prefixes and named scalar callees;
J8388 checks both standard-axiom audits. No concrete large term is reduced.

Only this worker's newly introduced Env J sources/objects are replaced in
these stages, with snapshots in its branch-owned host directory. The
predecessor cache is reused. Every host job uses 6G/8G/no-swap/64-task limits;
Rust uses four jobs and the required linker flag, with expected work in
translation/compilation/bounded verification rather than dense arithmetic.

## Verbatim headline before/after

No binder is discharged by the new reference-only results. Both execution
joins and the unrestricted observer program remain literally unchanged.
`headline-deletions.diff` is empty; the complete before/after module bytes
are identical. Quantifiers, carriers, bad events, and conclusion are unchanged.
The ideal-side `G_sim_R_wire` remains a named premise.

Before (verbatim):

```lean
theorem privacy_headline_admitted
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : (source).Adversary) (w : (R0Z.ZkStatement.HonestProver.Instance h)),
      (R0Z.ZkStatement.HonestProver.public h w) = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos
          (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : (source).Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x))
      (idealTestS (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100 := by
  exact PrivacyR1HeadlineOwnedClosed.privacy_headline_owned_closed template input outputs x
    builder_premises observer_program
    R_wire_builder_checker_D75_retry G_sim_R_wire

```

After (verbatim):

```lean
theorem privacy_headline_admitted
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : (source).Adversary) (w : (R0Z.ZkStatement.HonestProver.Instance h)),
      (R0Z.ZkStatement.HonestProver.public h w) = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos
          (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : (source).Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x))
      (idealTestS (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100 := by
  exact PrivacyR1HeadlineOwnedClosed.privacy_headline_owned_closed template input outputs x
    builder_premises observer_program
    R_wire_builder_checker_D75_retry G_sim_R_wire

```

## Single frozen final Lean replay

`harness/validate.py --check` passes source-manifest validation, exact generated
Funs identity, accepted-axiom checks, unchanged headline bytes and the
proof-only Rust source scope. The exact next consumer is
`R1Z.ProverCommit14Audit`, importing part 13 and every adopted new module.
No large numeral, recurrence cell or generated finite carrier is evaluated.

The single final replay is **J8389**, target **R1Z.ProverCommit14Audit**:
exit **0**, wall **1.88 s**, peak RSS **4114748 KiB**, **zero swaps**.
Source revision **`21a188d07`** contains the adopted dependency sources;
the additive audit is pinned by its exact source SHA and literal snapshot.
All 33 printed audits, including the unchanged admitted headline, have only
`propext`, `Classical.choice`, `Quot.sound`, or a subset. The full source
hashes, dependency fingerprint, target, status, timing, RSS, swaps and axiom
lines are committed in `lean/attempts-8389-8390.jsonl` and verbatim logs.
No unchanged full regression is repeated. Assigned Env J attempts are
consumed through **8389**; next available **8390**.

This is a coherent cached Lean dependency replay of this proof-only addition,
not a fresh shipped-runtime or frozen-ELF security certificate. Existing
adversarial/runtime/SBF evidence is reused because those covered production
inputs are unchanged. No local Lean compile, wallet/key cleanup, push or
merge is performed. Host caches and keys are retained.
