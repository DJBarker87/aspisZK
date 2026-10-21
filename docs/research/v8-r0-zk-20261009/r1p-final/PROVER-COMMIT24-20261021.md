# Prover commitment part 24

Base `0b214bdbd`; branch `codex/cx-prover-commit24-20261021`.

Target not yet established. This report is updated after each verified stage.
No file under crates/ or programs/ is edited. The concurrent worker's
SourceIdentification, RustRuntimeJoin and PrivacyR1FinalRelease are not edited.

## Stage 1 — explicit trusted std list

`R1Z.ProverCommitTrustedStd24.TrustedStd` names BTreeMap empty, insert state,
insert previous answer, get, ordered iteration, live-key TLS access and the
single-thread schedule. Every map contract is universal. No field contains
RustProverRefinement, a privacy conclusion, a source caller equation or a
coupling. This is the D133 std trust boundary alongside P6/P7, not a proof of
B-tree internals. It does not enlarge the trusted boundary to samplers.

The API is the successful-operation interface; allocator behavior remains
P6. TLS is one live, typed key, with no thread/key destruction during the
invocation. Trace and PROGRAMMED keys require distinct instantiations.

J7487 is an excluded section-variable elaboration failure. J7488 passes
`R1Z/ProverCommitTrustedStd24.lean`: exit 0, wall 1.40 s, peak RSS
2533360 KiB, swaps 0. All six theorem audits use only
[propext, Classical.choice, Quot.sound]. The exact source SHA-256,
dependency fingerprint, base revision and full audit lines are committed in
`evidence/prover-commit24-20261021/lean/attempts-7487-7489.jsonl`.
The model consistency theorem witnesses a satisfiable list; it supplies no
Rust evidence. No shared predecessor source/object was overwritten.

## Stage 2 — source nonzero counter and adaptive map callers

`ProverCommitCounter24.accounting` proves the exact retained counter for
successful finite executions of the actual extracted coin transition,
counting rejected zero answers. `three_search_room` applies to the three
successive nonzero calls in `sim::tape`, on stream 3 with one counter. If
each finishes within five draws, the final counter is their sum, at most 15,
and another five-word window cannot wrap. `three_agrees` composes all three
finite searches, preserving the counter between them. No unconditional
termination, unrelated-history freshness or whole sim::tape join is asserted.

J7489/J7490 are excluded scalar elaboration failures. J7491 passes the
six-theorem counter module: exit 0, wall 2.03 s, peak 4042632 KiB, swaps 0,
standard three axioms only. Exact receipts and failed sources are retained.

`ProverCommitMapProgram24.run_decode` goes beyond fixed write schedules:
it transports arbitrary finite callers that branch on previous insertion
answers, gets and full ordered iteration. It retains the decoded final
map, every ordered response and terminal output (including caller-selected
errors). `empty_run` uses the trusted empty-map field. The single named
TrustedStd premise supplies every library contract. Source caller-to-program
identification remains separate. J7492 passes: exit 0, wall 1.32 s,
peak 2534100 KiB, swaps 0; both audits use only standard axioms.

The retained ordinary/gamma transcript packets explicitly cover candidates,
not unconditional equivalence to the frozen source. They are not installed
as shipped policies. Further caller/policy/coupling work is below.

## Stage 3 — source-frame freshness and fuel marginal obstruction

`ProverCommitFreshWindow24.source_window_fresh` proves Fresh for a concrete
five-counter source address window against retained earlier coin coordinates
and observer queries outside the existing seedGuess event. Different attempts
and streams, and strictly lower counters on the same attempt/stream, are
separated on actual concatenated bytes. The start may depend on earlier
answers: all answer branches satisfy the invariant. This closes that local
freshness shape; it does not classify every other internal source hash call
or assert that the entire shipped caller is the marked program.

J7493 hit the existing heartbeat limit during implicit address reduction.
The replacement keeps the address definitions locally irreducible and
explicitly rewrites their small outer shape; no limit was raised. J7494 and
J7496 are excluded elaboration/projection failures. J7498 passes all five
freshness theorems: exit 0, wall 1.95 s, peak 4040884 KiB, swaps 0; standard
axioms only.

`ProverCommitFuelFactor24.runJoin_not_model_function` proves a necessary
coupling constraint for the actual RunJoin carrier: its retained fuel tape
cannot be any deterministic function of its model coins and retained seed.
The proof uses an off-graph witness and the exact product marginal; it never
enumerates the fuel carrier. `tape_nontrivial` needs no axioms. J7495 is an
excluded eventMass elaboration failure; J7497 passes the three theorems:
exit 0, wall 1.78 s, peak 4035376 KiB, swaps 0; standard axioms only.

This is a demonstrated obstruction to the deterministic-factor construction,
not a proof that a source coupling with additional randomness is impossible.
The generic complete_joint law does not by itself construct the two
RunJoin marginal maps for the actual source experiment.

## Concrete experiment and endpoint — not constructed

The requested shippedProverExperiment and both full RunJoins are still
unconstructed. Therefore there is no sound deletion-only specialization and
no new deployed endpoint with only TrustedStd and P6/P7. The new trusted
record is consumed by the local map/TLS endpoints; it is **not yet a premise
of a new deployed privacy endpoint**. This portion of item (1), and items
(3)/(4), remain incomplete. No hidden source join is added to TrustedStd.

There are two concrete obstructions to the immediately available adapters:

1. The retained raw `sampler.add_small_base_p` wrapper applies
   `into_iter_back back`. The external ABI expects an iterator state;
   `back` is a state transformer. J7499's `#check_failure` reproduces that
   type mismatch with the actual Aeneas IterMut type. `into_iter_back
   (back iter)` is typed, but the retained packet labels that manual repair
   a compatibility candidate and leaves whole traversal/source equivalence
   open. The gamma/ordinary candidate theorems cannot be installed as
   current frozen policies on that evidence. This is an obstruction to
   reusing that packet, not a claim that frozen Rust gamma is incorrect or
   impossible to verify. No Rust sampler was changed or adopted.
2. `runJoin_not_model_function` formally rules out filling the extra retained
   fuel Tape from model coins/seed. A different construction with additional
   randomness and both proved marginals is needed. Generic adaptive-history
   equality alone is not that construction.

The current caller still needs unconditional, source-pinned gamma/ordinary/
query policies, the circle caller and nominal carrier joins, classification
of every internal prior hash address, retries/errors/serialization and native
trace identification. The local bound proves counter room on good finite
searches; it does not prove source-event containment or an independent model/
seed/fuel factorization. The map library internals are no longer a proof
obligation under D133, and no further B-tree gate was run.

The next source deliverable is a typed current sampler adapter with a proved
Std mutable-iterator/writeback instance (or a source-preserving equivalence
to a verified owned helper), not an assertion of candidate equivalence. Then
assemble the actual finite source experiment and its two marginal maps.
The permitted std trust item does not discharge those source obligations.

## Verbatim endpoint before/after

No specialization occurred. Both statements below are the literal deployed
fuel-endpoint definition and theorem signature. Their byte equality is
checked by the final audit. The deletion-only diff is empty; it removes no
premise and is **not** the requested successful specialization. Quantifiers,
carriers, bad events and conclusion are unchanged.


Before (`0b214bdbd`):

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After (this branch):

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

## Final verification and evidence

J7499 compiles `R1Z/ProverCommit24Audit.lean`: exit 0, wall 1.71 s,
peak RSS 4095704 KiB, swaps 0, source revision `0ba397704` plus its exact
additive audit source SHA-256/dependency fingerprint. All 24 complete axioms
lines (22 new theorems and both unchanged deployed endpoints) use only
[propext, Classical.choice, Quot.sound], or no axioms. The expected
`#check_failure` prints the raw ABI diagnostic; it declares no theorem and
introduces no axiom. The repaired expression's successful type check is not
a source-equivalence certificate.

Every attempt 7487–7499 has its exact source snapshot, SHA-256, transitive
owned dependency-object fingerprint, source revision, exit, wall time, peak
RSS, swap and complete axioms/error lines in the committed `lean/` receipts.
All jobs ran on Env J with the global lock, one Lean job at a time, under
6G/8G/no swap/64-task scopes and -M7000. No limit was raised. Only this
worker's new modules/objects were updated; their consumers use the final
objects. No source or object owned by the concurrent worker was changed.

Only the final changed-cone audit ran once. A complete frozen release replay
is withheld because the concrete source closure is not green. No Rust test,
Aeneas regeneration, or ELF rebuild was run. Files under crates/ and programs/
are unchanged from `0b214bdbd`; unchanged-source D129 ELF evidence is reused,
without making a new binary equivalence claim. No key or wallet was touched.
No binaries, objects or archives are committed. No push. All SSH calls
completed well within the twenty-minute no-output limit.

`harness/final-audit.py` checks the accepted/excluded receipts and exact
source snapshots, all final axioms lines, unchanged endpoints, the verbatim
report statements, resource launcher settings, sampler wrapper provenance
and untouched shipped/concurrent-owner files. Its output is `final-audit.json`.

The packet consumes 7487–7499. Next candidate: 7500, subject to receipt check.
The release target is unchanged and **not yet established**.
