# Prover commitment part 26

Base `57ca9c452`; branch `codex/cx-prover-commit26-20261021`.

Target not yet established. This report is updated after each verified stage.
No shipped file or concurrent-owned module is changed.
The last, job-specific attempt assignment 7584–7699 takes precedence over
the earlier overlapping ranges; check the shared receipts before each use.

## Stage 1 — split arithmetic gates

Pending: verify the exact paired division cell, then its verified-stub limb
caller, then Lean induction over limb/digit schedules. The 600/180-second
predecessor gates remain excluded; neither is rerun unchanged.

The exact arithmetic-cell contract passes (`cell-v1`): all `u64` remainder
and `u32` limb inputs satisfying pairwise equality, using the two literal
shift/or/division/modulo expressions, return equal quotients and remainders.
Exit 0, wall 30.733 s, peak RSS 132804 KiB, swap 0. `limbs-v2` uses
`stub_verified(paired_cell)` for the reverse-iterator/decrementing-index
product, retaining all eight output limbs: exit 0, 0.899 s, 148056 KiB,
swap 0. `limbs-v1` is an excluded missing-stubbing-feature compiler error.
All Rust gates use the requested 6G/8G/no-swap/64-task cap and RUSTFLAGS.

`ProverCommitLowDigits26.limbs` proves the symbolic loop invariant for the
iterator fold, including an arbitrary previously written quotient prefix.
`pass` identifies the whole fold with the existing machine-process model;
`digits` proves all remainders and the entire retained quotient equal for
any number of digit passes. `low_digits`, `remaining`, and `canonical`
transport the existing arithmetic meaning. J7585: exit 0, wall 0.87 s,
peak RSS 1711236 KiB, swap 0; all six axioms audits use only the standard
three axioms or fewer. J7584 is an excluded reserved-identifier parse error.
Exact sources, revisions and dependency fingerprints are in `lean/`.

Two array-valued contract experiments (`pass-v1`, `pass-v2`) were stopped
near 6.1 GiB process RSS before increasing pressure. They are excluded;
the second changes the independent-input precondition into a shared input.
Neither improves the successful small limb harness. These diagnostics are
retained with source snapshots and resource receipts. No cap was raised.
The useful replacement is the small verified-cell product plus symbolic
induction; no full arithmetic network is replayed.

Scope: the new Lean induction is a machine/list-model theorem. Source
binding still relies on the separately checked control skeleton and P6;
it is not a new Aeneas theorem identifying the original iterator body with
the extracted indexed body. This distinction must remain visible at the
whole-source boundary. No endpoint premise is removed at this stage.

## Stage 2 — concrete query callback and extracted continuation

`ProverCommitQuery26.policy` installs the concrete query callback along with
all three scalar policies from part 25; no query callback parameter remains.
It uses the retained concrete LE/mask decoder, list scanner and first-stop
driver, starting at the explicit zero scanner. `success` supplies both the
selected-state driver trace and the full concrete Q22-valid per-block chain.
`rejection` maps scan failure to Transcript. `caller` factors the *actual
extracted* eager sixteen-read schedule from this concrete callback and the
literal 22-entry trace continuation; it retains all failure/divergence cases.
`finish_rejection` proves that query failure retains the absorbed state and
previous trace. These are owned-source/model facts, not a shipped FS experiment.

J7615 passes all six top-level audits: exit 0, wall 4.35 s, peak RSS
4030576 KiB, swap 0; only [propext, Classical.choice, Quot.sound].
The source factorization is checked byte-for-byte by `harness/check-query26.py`.
The proof uses shallow bind congruence with explicit tuple normalization;
it does not raise depth/heartbeat options. J7601–7614 retain all failed
elaboration/normalization diagnostics and exact snapshots.

Thirteen retained query owners are now compiled from pinned source into Env J,
coherently with the installed scalar/source closure. J7586–7589, J7592–7600
pass. J7590 is an excluded monadic elaboration port failure; J7591 is a
preflight-only missing dependency. The driver proof port replaces inferred
pair-bind elimination with explicit bind elimination; no statement or
executable body changes. `query-owners.json` and `query-ports/` pin every port.

Source/library gates: `query-iterator-v1` proves all eight actual IntoIter
values and exact exhaustion (0.598 s, 145840 KiB); `query-decoder-v1` proves
source from_fn/map versus ordered LE/mask parsing (0.789 s, 168940 KiB);
`query-driver-v1` proves outer loop versus first-stop unrolling, including
all observed block bytes and selected advance bytes, for arbitrary stop
responses (6.572 s, 389884 KiB). Every gate exits 0 with zero swap.
The driver's scan callback is abstract: this is a control theorem, not an
assertion that the complete native scanner equals its model.

The direct complete eight-word scanner comparison timed out at 90 s;
its variable-prefix membership diagnostic timed out at 60 s. Neither counts
as verification. Replacing the symbolic slice length by *every* fixed length
0 through 22 yields 23 successful source-contains/explicit-membership gates:
1.18–1.65 s each, under 267000 KiB, zero swap, with unwinding assertions.
The complete old scanner gate is not rerun. These fine-grained gates close
library/control obligations; their full source-to-Q22 composition still needs
an exact scanner execution transport theorem. The standard trust list is not
expanded to include that desired conclusion.

### Unconditional query reference totality

`ProverCommitQueryTotal26` removes the successful-call premise at each
construction layer: generic stateful from_fn totality, concrete byte-rank
and masked-word totality, valid scanner transition totality, first-stop
finish totality, the complete eight-block driver, and finally the installed
query callback. All input bytes remain universally quantified. Query rejection
is retained as a normal result, not assumed away. This closes the totality
of the concrete policy, while source correspondence remains a separate claim.

J7621: exit 0, wall 2.49 s, peak RSS 3987544 KiB, swap 0; all nine audits
standard-only. J7618 and J7620 are focused predecessors (2.01/2.45 s,
3974852/3981816 KiB, zero swap). J7616/7617/7619 are excluded elaboration
failures. Source snapshots, dependencies, errors and complete audit lines
are retained in the per-attempt evidence. No new depth/heartbeat limits.

## Stage 3 — semantic/circle validator transport

`ProverCommitSemanticTransport26` identifies the independent nominal owners
of WideExact decoding and record validation. `limbs`/`bytes` retain every
canonicality rejection and machine failure; `zero_test` preserves the exact
QM31-subfield check. `fields_bounded` proves the recursive field validator
transport by a symbolic payload-length induction, and `fields` removes the
bound by choosing a sufficient symbolic fuel. `checked` transports the full
header/tag/length/canonicality checker for every row and byte slice, including
all errors and divergence. `shape` preserves every row shape and its constants.
This closes the checker-conversion obligation left open in part 25; it does
not itself identify the whole shipped prover/simulator continuation.

J7630 passes all eleven audits: exit 0, wall 8.85 s, peak RSS 3991592 KiB,
swap 0; standard axioms only. Focused predecessors J7623/J7624/J7626 passed
at 1.92/2.03/2.28 s and 3967516/3968240/3972160 KiB, zero swap.
J7622/J7625/J7627–7629 are excluded elaboration/normalization failures.
No recursion/heartbeat option changed and no concrete large arithmetic was
normalized. Only this job's additive modules were installed; imported shared
predecessors and all concurrent-owned files remain untouched.

## Stage 4 — install the coupled source oracle in extracted digest APIs

`ProverCommitDigest26` constructs concrete, total ROM interpretations for the
semantic, circle and suffix `Digest32` owners. All three concatenate the exact
ordered source slices and return the retained machine byte representation of
the same oracle answer. `semantic_circle` proves the nominal hash instance
conversion exactly. `packed_read` installs the product coupling's packed raw
words at their actual stream-3 addresses. `digest_law` proves that the *whole
installed digest function*, as a consumer of the complete finite table, has
the uniform source-table law. It supplies no source/model execution equality
and adds no trusted source-join field.

J7632 passes all four audits: exit 0, wall 1.98 s, peak RSS 4074312 KiB,
swap 0; standard axioms only. J7631 is an excluded namespace/dictionary
elaboration failure. The replacement uses the existing explicit finite-instance
transport and opaque finite dictionaries, preserving the actual distributions
without kernel-normalizing their large enumerations. No limits were raised.
The dictionary linter warnings concern intentional opacity, not added axioms.

## Demonstrated obstruction — stateful ideal oracle versus pure extracted API

The native simulator's `CoinOracle::digest` (`crates/aspis-r1-cost-probe/src/sim.rs`)
borrows a `RefCell<CoinState>`, reads `coins[next]`, increments `next`, and may
also update the recorded table/collision flag. It does this even for a repeated
input. The current extracted semantic/circle/control `Digest32` operation has
type `H → Slice (Slice U8) → Result Bytes32`; it returns neither an updated
handle nor an updated heap. The new pure shared-ROM instances correctly
interpret a lookup oracle, but **cannot unconditionally interpret this native
cursor oracle**. This distinction was found during source composition; the
new digest law must not be promoted to the simulator's full execution law.

`oracle-effect-v1` copies `concat`, `CoinState` and `CoinOracle::digest`
verbatim from pinned source, adds only the trait/type wrapper and a test,
and runs the exact same input twice against coins `[zero, one]` with recording
disabled. It observes zero, then one, and cursor two. The optimized native
counterexample passes: exit 0, wall 0.362 s, RSS 126864 KiB, swap 0,
6G/8G/no-swap/64-task scope, requested RUSTFLAGS. This is a concrete source
counterexample to a stateless interpretation, **not** a privacy attack or an
end-to-end counterexample. `oracle-effect-source.json` pins the copied bodies.

`ProverCommitOracleEffect26.two_reads` proves the corresponding cursor trace.
`no_stateless_interpretation` proves that the *actual extracted API* cannot
return both distinct answers for the same handle and parts. J7634: exit 0,
1.85 s, 4070944 KiB, zero swap, both standard-only axioms audits.

This stops the direct ideal-side instantiation in stage (3). Repair requires
an explicit state/heap-threaded interpretation or a proved execution transport
for `CoinState.next`, recording and collision behavior, composed through the
semantic/circle/suffix calls. A freshness restriction cannot be silently
assumed or added to TrustedStd. If freshness is used, it must follow from the
existing permitted exceptions (or a separately justified change to the stated
bound); it is not supplied by the totality or marginal theorems above.
The source file and extraction interface are unchanged; no protocol or
security-contract change is proposed here.

`shippedProverExperiment`, its complete real-side and ideal-side WholeRunJoins,
and endpoint specialization remain **unconstructed**. Beyond the effect
transport, the exact builder/checker/retry, native trace, commitment programming
and ordered serialization continuations still need their full observable
source/model identification. The new component results close local obligations
only. TrustedStd has not acquired a source-refinement field, and P6/P7 have
not been broadened to assume the desired conclusion.

## Coherent verification and scope

J7635 passes `R1Z/ProverCommit26Audit.lean`: exit 0, wall 1.75 s,
peak RSS 4115124 KiB, swap 0, source revision `39e78e853` plus the exact
additive source snapshot SHA-256/dependency fingerprint in its receipt.
All 40 complete audit lines (38 new facts and both retained endpoints) use
only [propext, Classical.choice, Quot.sound], or fewer. The source-level type
inventory records the actual FSExperiments and extracted continuation types.
J7633 is an excluded audit diagnostic: its 38 checks were standard-only,
but an unimported assembly-name `#check` failed. J7635 changes the audit source
by removing that diagnostic and adding the two new effect-obstruction facts;
it is not an unchanged rerun. The final changed dependency closure is coherent.

All actual Lean attempts (including failures) record target, source snapshot,
revision, source hash, dependency fingerprint, exit, time, RSS, swap and full
axioms/error output. J7591 is preflight-only. All host Lean compiles used one
job at a time through the global launcher lock and the required scope caps;
Rust gates use independent capped scopes. Later Rust gates record prelaunch
aggregate checks in the retained runner; the early cell scope was observed at
34.375 GiB aggregate reservation, within the 55 GiB host limit. No cap, heartbeat or recursion limit was raised.
The final summary is `final-audit.json`; `rust-inputs.json` binds every Rust
gate to its source snapshot. Timeout parent RSS omits killed descendants;
the cgroup peak in each receipt is authoritative for those failed probes.

No tracked file under `crates/` or `programs/` changed. The shipped-file ELF
rebuild rule is not triggered; unchanged D129 artifact evidence is reused,
without claiming a new ELF comparison. No concurrent-owned module, wallet
or key was touched. No binaries, objects, archives or local target directory
are committed. No push. The complete frozen release manifest is withheld
because the concrete whole-source refinement has not passed its preflight.
Next Env J candidate: 7636, subject to the shared receipt check.

## Verbatim endpoint before/after and deletion-only diff

The specialization is blocked as described above. The endpoint declarations
below are copied verbatim from `ProverCommitDeployedFuel22.lean`; surrounding
parameters and local notations are unchanged. Before is base `57ca9c452`;
after is this branch. The entire endpoint module is byte-identical.
`endpoint-deletion.diff` is empty: zero premises removed. This is **not** a
successful deletion-only discharge; no quantifier, carrier, exception or
conclusion was changed.

Before:

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

After:

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

The requested deployed target is **not yet established**.
