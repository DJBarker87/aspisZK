# Prover commitment part 19 — seed event and shipped experiment

Base `28776b162`; branch `codex/cx-prover-commit19-20261021`.

Work in progress. Target not yet established. This report is updated at each
committed stage. Concurrent-worker modules SourceIdentification,
RustRuntimeJoin and PrivacyR1FinalRelease are untouched.

## Scope and mathematical accounting

D127 authorizes a seed-guess exception and its explicit privacy loss. The
constructed model has no simulator-seed coordinate; the new event must use
an independent retained seed, rather than assuming that an existing model
coordinate is independent of its own observable history. The global event
must be counted once, outside the eight-attempt union.

## Evidence

Focused Lean checks run on the NUC, one at a time, in env J using unused
attempts 8675–8799. Each scope has MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0 and TasksMax=64. Exact snapshots and JSONL receipts are stored
in `docs/research/100bit-spend-path-20261013/evidence/prover-commit19-20261021/`.
No full frozen-manifest replay is claimed until the focused dependency cone
is green. Source revision, exit, wall time, peak RSS, swaps, dependency hashes
and full axioms lines are retained in the per-attempt receipts.

## Stage 1 — seed accounting and premise transport

`ProverCommitSeedEvent19.seedPoint` tests the exact source domain and 32-byte
seed prefix. It deliberately also charges malformed suffixes in that namespace.
`source_point` proves containment of every source coin address, for every
attempt, stream and counter. `seedPoint_unique` proves that any query names
at most one seed. `seed_mass` proves the resulting q/2^256 upper bound for a
list depending arbitrarily on all model coins and adaptive answers, independent
of the separately retained seed. No seed carrier is enumerated.

`augmented old queries i (m,seed)` is
`old i m ∨ (i = 0 ∧ seedGuess (queries m) seed)`.
`old_contained` and `union_mass` prove containment and a single global charge,
not eight charges. `ProverCommitSeedJoin19.of_old` constructs an actual product
extension of the old coupling; the runtime/model observations do not change.
This proves implication of old certificates to augmented certificates. Proper
inclusion for each adversary is not asserted (an observer making no queries
has no seed-guess event).

`ProverCommitObserverQueries19` exposes the exact adversary-only `runLog`
suffixes in real and ideal games, including failure exits; both lengths are
at most W.qmax. The query functions retain the original shared table and
programmed fallback. They do not replace adaptive queries by fixed addresses.

Accepted focused checks: J8681 seed events (exit 0, 2.12 s, 4,042,740 KiB),
J8683 generic join/numerics (exit 0, 2.45 s, 4,060,364 KiB), J8685 query caps
(exit 0, 2.05 s, 4,037,844 KiB). All swaps 0; all printed axioms are subsets
of `[propext, Classical.choice, Quot.sound]`. Revisions are `28776b162` plus
exact snapshot hashes. Earlier attempts are retained and excluded: the errors
were local rewrite/decider/instance normalization, repaired without changing
resource limits. Existing shared objects were not overwritten in this stage.

The numerical proof is symbolic: at q ≤ 2^64, one seed charge is at most
2^-192; two coupling sides add at most 2^-191. The old conservative upper
bound plus these terms is at most 8·2^-109 = 2^-106 < 2^-100. No old loss is
removed or hidden. Connecting this result to the deployed signature is the
next stage; concrete shipped execution and full simulator history remain open.

## Stage 2 — deployed endpoint with explicit seed events

`RustProverRefinement` now uses `ProverCommitSeedJoin19.RunJoin`: its model
randomness is the existing model randomness times an independent uniform
32-byte seed. Its agreement includes the whole ROMView and observer decision
outside `augmented oldBad fixedQueries`. The query suffix functions fix the
ordered source observer and include abort exits. `LegacyRustProverRefinement`
is the verbatim old premise; `legacy_refinement_implies` proves its implication
to the new premise with unchanged observations, using product extension.
No source refinement has been assumed or discharged by this transport.

The privacy error and its upper bound now explicitly add
`2 * ProverCommitSeedEvent19.budget (2^64)` = 2^-191: one global seed charge
for each of the real and ideal coupling comparisons. Each charge covers the
entire eight-attempt run. Keeping the real-side allowance too is conservative;
neither charge is multiplied by eight. All old error terms are retained.
The result remains strictly below 2^-100.

J8688 passes: exit 0, 12.70 s, peak RSS 4,203,096 KiB, swaps 0, revision
`b1978fda4` plus exact source snapshot hash; standard axioms only. J8686–8687
are excluded local annotation errors. The shared deployed source/object was
snapshotted under the part-19 host workspace before replacement. New consumers
must use this new dependency; this is not evidence for an unchanged old olean.
No concurrent-owner module is edited or replayed.

The exact before/after full files are `endpoint-before.lean.txt` and
`endpoint-after.lean.txt`, and the complete change is `endpoint.diff` in this
pass's evidence directory. The following are the verbatim new top statements.

```lean
theorem legacy_refinement_implies
    (old : LegacyRustProverRefinement template outputs x rust observer_program) :
    RustProverRefinement template outputs x rust observer_program

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) < 1 / 2^100
```

## Stage 3 — joint histories rather than marginal coins

`ProverCommitJointHistory19.swapCoordinates` is an actual equivalence: it
exchanges the independent coin vector with the corresponding entries of the
single shared oracle table. `seededCoupling` retains the seed and proves both
whole marginal laws exactly. `replace_at` recovers every source coin from the
same replaced table; `replace_off` retains all other oracle answers.

`runLog_agrees` inducts over the adaptive program, preserving the complete
ordered address/answer history, repeated queries and early exits.
`byte_history_agrees` specializes this to the actual 65-byte simulator coin
frames, all eight attempts, all four streams and any bounded counter schedule.
`programmed_history_agrees` additionally retains an arbitrary coin-dependent
programming table before the shared-oracle fallback. `joint_observation`
retains an arbitrary public view of all the coins, so deterministic bounded
retry, acceptance, error and serialization projections can be included in it.

`componentJoin` constructs the complete component RunJoin with only the
single seed exception; its pointwise lookup obligation is discharged for the
source byte table by `byte_oracle_agrees`. This is the joint law missing in
part 18. It is not yet a source identification of the full simulator: the
bounded coordinate schedule, actual view calculation and uncapped source
nonzero loop still need their source certificates. No RustProverRefinement
premise is removed, and no shippedProverExperiment is claimed.

J8694 passes the final enhanced module: exit 0, wall 2.27 s, peak RSS
4,043,648 KiB, swaps 0, revision `59790da74` plus exact source hash; all
printed axioms standard (exchange has none). J8689/J8690 checked earlier
versions; J8691–8693 exposed local elaboration issues, retained and excluded.
The replacement avoids reducing concrete finite address/coin enumerations;
no recursion or heartbeat limit was changed. These are focused component
checks, not a coherent frozen release replay.

Verbatim joint equality and coupling statements follow; the full RunJoin
constructor is in the source snapshot.

```lean
def seededCoupling {S : Type} [Fintype S] [Nonempty S]
    [Fintype A] [Fintype I] [Fintype U] [Nonempty U]
    (key : S → I → A) (injective : ∀ seed, Function.Injective (key seed)) :
    Coupling (S × (A → U)) (((I → U) × (A → U)) × S)

theorem joint_observation {count : Nat} (room : count ≤ 2^64)
    (bound : Nat) [Fintype (RomFiniteBin.Address bound)] (fits : 65 ≤ bound)
    {V : Type} (view : (ProverCommitSimulatorOracle18.Index count → OracleAnswer) → V)
    (program : V → OProg) (fuel : Nat)
    (seed : OracleAnswer) (coins : ProverCommitSimulatorOracle18.Index count → OracleAnswer)
    (table : RomFiniteBin.Address bound → OracleAnswer)
    (fresh : ¬ seedGuess (runLog (program (view coins)) (RomFiniteBin.lookup bound table) fuel) seed) :
    let key := ProverCommitSimulatorOracle18.key (count := count) bound fits seed
    let hinj := ProverCommitSimulatorOracle18.key_injective room bound fits seed
    let sourceTable := replaceTable key hinj coins table
    let sourceCoins := fun i => sourceTable (key i)
    (view sourceCoins, runLog (program (view sourceCoins))
      (RomFiniteBin.lookup bound sourceTable) fuel) =
    (view coins, runLog (program (view coins)) (RomFiniteBin.lookup bound table) fuel)

theorem programmed_history_agrees {count : Nat} (room : count ≤ 2^64)
    (bound : Nat) [Fintype (RomFiniteBin.Address bound)] (fits : 65 ≤ bound)
    (seed : OracleAnswer) (coins : ProverCommitSimulatorOracle18.Index count → OracleAnswer)
    (table : RomFiniteBin.Address bound → OracleAnswer) (entries : List Entry)
    (program : OProg) (fuel : Nat)
    (fresh : ¬ seedGuess (runLog program
      (programmedOracle entries (RomFiniteBin.lookup bound table)) fuel) seed) :
    runLog program (programmedOracle entries (RomFiniteBin.lookup bound (replaceTable
      (ProverCommitSimulatorOracle18.key (count := count) bound fits seed)
      (ProverCommitSimulatorOracle18.key_injective room bound fits seed) coins table))) fuel =
      runLog program (programmedOracle entries (RomFiniteBin.lookup bound table)) fuel

```
