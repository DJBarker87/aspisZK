# Part 49: native simulator payload composition

**Target not yet established.** Branch `codex/cx-prover-commit49-20261022`.
Scope: semantic samples and guards, final shift, weight-model correspondence,
and native caller composition. No FSExperiments conversion or joins.
Fresh authorized range J10000–J10199 supersedes the earlier range in the prompt.
No shipped source changes are planned; any such change triggers all three
frozen ELF rebuilds against 40dc7574… / 12cb0bc2… / 121f3e29….

## Validation

Host-only focused Lean attempts, one module each; native gates and extraction
run in MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64 scopes with
RUSTFLAGS='-C link-arg=-Wl,--threads=4'. Every actual attempt retains its
source, dependencies, exit, time, RSS, swaps, revision and printed axioms.

## Stage 1: oracle-result sum and final shift kernel

J10009 proves `SampleSum49.sum_value` / `partial_sum`: the entire owned
counter returns a canonical QM31 with the exact ordered sum, for every
prefix up to 512 explicit oracle results. The semantic oracle-result provenance
is still an independent caller obligation; no oracle law or payload identity
is supplied by this theorem. J10011 proves `Shift49.shift_value` and
`polynomial_shift`: the two updated coefficients represent exactly
`p + C ((original-eta0)*inv) * (X-C half)`. This is after the inverse returns;
its native inversion contract and the semantic meanings of the inputs remain.
Both accepted files print only [propext, Classical.choice, Quot.sound].

Native Kani passes: tail transition (0.315 s / 134004 KiB), oracle sum with
both success/error (0.408 s / 140912 KiB), and complete 10x28-array shift
context (2.832 s / 288000 KiB), all zero swaps. Universal arithmetic answers
are paired with exact operand/call traces. No arithmetic truth is inferred
from those callee stubs. `pins/native-spans.json` records source and control
abstractions. The counter owner alone is extracted; shipped code is not.

The first Charon run accidentally includes unused field iterator declarations
and reports four trait transformation errors. Restricting its root to the
new owned module removes them. The first Lean extraction exposes a backend
usize shift-count mismatch; an explicit u32 cast fixes the owner. The retained
arithmetic bodies are checked against the release extraction; newly reached
literal constants/embeddings are emitted exactly. J10000/04/07/08/10 are
rejected drafts, with diagnostics retained. J10001 is a missing-dependency
preflight refusal; J10002/05 are unchanged-input launcher refusals, with no
compiler executed. Those numbers are retired. J10003/06 validate the owner
bindings; the latter reuses the already-defined ONE from Basis to avoid an
import collision. Every overwritten shared source/object is snapshotted by
the launcher; no prior theorem's source body is changed.

No pure std trust fields added. No shipped files changed. Target remains open:
semantic point/oracle correspondence and guards, inverse binding, weights,
all remaining native callers and complete ordered model payload image.

## Stage 2: exact sample-point and Boolean enumeration correspondence

J10014/16/18/21/25 establish the scalar bit interpretation, the complete owned
tail update, the complete sample point, the big-endian assignment bijection,
and the equality of the sample-point sum with the existing model's
`HonestView.roundPoint` sum. `SampleModel49.point_model` assumes only the
already-received challenge prefix, not a point-array or sample-output image.
`sum_points` transports arbitrary point functions; the actual native semantic
oracle still needs its value/success law. The explicit owner shift-count cast
is checked by `tail-cast-v2` (0.331 s, 134216 KiB, zero swaps).
J10026 proves boundary preservation and terminal adjustment of the shifted
polynomial, with the half and inverse/nonzero conditions exposed. It does not
claim those conditions or the native guard arithmetic have been discharged.

All accepted declarations print only standard axioms. Failed intermediate
syntax/carrier/simp drafts are retained. J10012 is a transient aggregate-memory
reservation refusal, before a compiler launch. The subsequent authorized
reservation succeeds; no cap or host reservation policy is changed.
No native source is extracted and no shipped file changes.

## Verbatim endpoint before/after: unchanged

The complete endpoint module, including every section binder, definition,
and theorem proof, is byte-identical in `endpoint/before.lean.txt` and
`endpoint/after.lean.txt` in the evidence directory. The following verbatim
excerpts retain the x/rust binders and complete theorem statement. No D146
domain restriction is installed before the source join exists; x and rust
still have their original quantifiers. No conclusion, failure event or bound
is changed, and RustProverRefinement remains explicit.

Before:

```lean
variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input
local notation "decode" => ownedDecode

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
  [Fintype rust.RealRand] [Nonempty rust.RealRand]
  [Fintype rust.IdealRand] [Nonempty rust.IdealRand]
  (observer_program : rust.Adversary → View K CommitHandle Aux R1Bat →
    List (List UInt8 × OracleAnswer) → OProg)

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
variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input
local notation "decode" => ownedDecode

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
  [Fintype rust.RealRand] [Nonempty rust.RealRand]
  [Fintype rust.IdealRand] [Nonempty rust.IdealRand]
  (observer_program : rust.Adversary → View K CommitHandle Aux R1Bat →
    List (List UInt8 × OracleAnswer) → OProg)

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```
