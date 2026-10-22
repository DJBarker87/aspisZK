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

## Stage 3: materialization and inactive contraction arithmetic

J10028 proves actual `WideExact::mul_qm31` for arbitrary raw QM31 RHS and
canonical full-width input, including constructor normalization. J10030 proves
the complete generic interval contraction; J10032 composes the actual kappa
power producer with all seven cell terms, and the complete 1024-term inactive
dot product. No power-array identity or source-success premise is supplied.
The raw weight entries are still inputs: these theorems do not identify
`Weights::raw` with the seven model functionals or prove the full materialized
array/caller. All accepted declarations print only standard axioms. J10029
and J10031 are rejected import/numeral/index-normalization drafts.
Native material-cell and inactive transitions pass on arbitrary full arrays
and legal indices (0.401 s / 139728 KiB; 8.484 s / 333680 KiB), zero swaps.
The raw-method result is explicit and arithmetic callees are universal paired
answers; no model-weight law is hidden in the stubs. Full copied field sources
remain byte-identical to the shipped files. No shipped file changed.

## Stage 4: actual optimized boundary arithmetic

The source boundary helper is a four-limb integer accumulator, not the old
QM31 addition chain. Native Kani checks its complete 28-coefficient accumulator
against four separated scalar owners, for arbitrary full u32 words: exit 0,
17.103 s, 1025404 KiB, zero swaps. The exact literal source accumulator and
source hash are retained in `pins/boundary-native-spans.json`. No field call
is stubbed in that gate; reduction is separately proved.
J10035 proves the complete scalar counter and current release reduction modulo
P. J10036 proves the reconstructed canonical QM31 equals twice coefficient zero
plus the remaining coefficient sum. J10038 composes all four scalar Results and
proves `BoundaryPolynomial49.exact_result`: the complete four-limb reference
returns a canonical value whose decode is p(0)+p(1), on arbitrary raw input
words. The native accumulator split and source reducer are the binding boundary;
this does not yet prove the semantic caller's boundary comparison succeeds.
J10034 and J10037 are rejected range/import drafts; J10033 checks extracted
owner definitions. All accepted declarations print only standard axioms.
The boundary owner's namespace is nominally rebound to `Boundary49` to avoid
an `owned.sum` collision; its arithmetic declaration bodies are unchanged.
No new trust field or shipped-source change.

## Stage 5: point-factor values and transported point weights

J10043 proves all four source-owned point/circle factor values and the exact
doubling factor. J10045 composes every factor of the five-entry product.
J10046 constructs the point factors from arbitrary canonical source point
coordinates, selects the radix-four digits, and proves the complete product
is the model's transported Boolean equality weight. There is no supplied
factor-array/model identity. This closes the arithmetic and model relation
of the point-factor helper chain; statement-point construction, full unsafe
Weights initialization and its source raw-index/caller composition remain.
The native raw-product transition passes at every legal S2 kind/digit/index,
with full factors and exact arithmetic operands (1.528 s, 157120 KiB, zero swaps).
J10041 is a focused namespace port of the retained D18 point-factor theorem
(the old `R1D18PointWeights` object is absent), with all private/public theorem
axioms printed. J10040 is that missing-object preflight, no compiler launch.
J10042/44 are rejected index/simplifier drafts. All accepted axiom lists are
standard; `quad_canonical` is axiom-free. No max options added. No shipped change.

## Stage 6: source statement points and their point-weight consumers

J10051 proves all ten successor carry transitions, canonicality and exact
`SemSource.successorPoint` value. J10052 proves both source absorption toggles
and the complete three-point output equal the existing model's
`openingPoints`, after the documented MSB/LSB reversal. J10053 composes this
producer with all three point-weight factor products. No statement-point
identity is supplied as a caller hypothesis. Full Weights allocation, factor
matrix initialization and remaining raw-kind/caller composition are still open.
J10047 checks the extracted counter definitions; J10048/49 are rejected
carry-index drafts. J10050 is a dependency preflight refusal, no compiler launch.
Native successor transition v2 passes (0.510 s, 145580 KiB), as does the complete
two-cell absorption (0.551 s, 157884 KiB); both zero swaps. Successor v1 is a
Rust mutability compile error, retained. All checks retain every input/output
coordinate, carry and arithmetic operand/call order. Accepted Lean axioms are
standard. No pure std contract or shipped-source changes.

## Stage 7: complete circle-factor rows and circle functional

J10055 proves the source bit-shift/mask digit equals the mathematical radix-four
digit. J10057/59 supply generic nested-array updates and exact line-factor rows.
J10061 composes every circle-fill stage; J10063 proves complete initialization
and all five canonical factor rows. J10072 proves selecting and multiplying them
is the selected natural-circle weight. J10069/74 identify that weight with the
model evaluator on a basis vector, including its WideExact embedding. No
constructor-factor/model-image equality is supplied. This is the circle helper
chain; full Weights storage/caller assembly remains open.

Native circle-fill transition: exit 0, 2.207 s, 149744 KiB, zero swaps. Native
point-factor expression: exit 0, 0.506 s, 145456 KiB, zero swaps. Both check the
full current state and paired arithmetic operand/order traces. The arithmetic
trace buffer grows to 16 for the nine-call fill transition; earlier evidence
retains its exact eight-entry snapshots. Aeneas' pure denotation shares repeated
equal arithmetic calls (point complements and double's mul(x,x)); the Lean
value laws use deterministic pure arithmetic. No source trace-count equality
is inferred from that denotation. L2 composition is outside this job.

J10062 ports the existing generic selected circle factorization without its
unused NeZero(2) binder. J10071 is the focused generic five-factor product.
The concrete draft J10064 and J10068 hit the default heartbeat limit during
carrier/index normalization. The replacement keeps field operations opaque,
proves the product over an abstract field, and rewrites finite indices and
Nat division by one explicitly. It passes in 1.10 s / 2169208 KiB. No cap or
option was raised. All final printed axioms are standard. Rejected drafts and
all diagnostics are retained. Factor extraction v2 adds only owned line/fill
functions; selected old factor/arithmetic declarations remain identical and
are rebound against v2 to keep the final input pin current. No shipped change.

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
