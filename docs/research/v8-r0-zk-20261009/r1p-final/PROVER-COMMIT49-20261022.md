# Part 49: native simulator payload composition

**Target not yet established.** Branch `codex/cx-prover-commit49-20261022`.
Scope: semantic samples and guards, final shift, weight-model correspondence,
and native caller composition. No FSExperiments conversion or joins.
Fresh authorized range J10000–J10199 supersedes the earlier range in the prompt.
All 491 shipped files are unchanged from the actual task base c6be35873ed67abf55956e4e2cac411260bea973. The shipped-file rebuild rule was not triggered; no fresh ELF rebuild is claimed. Retained release pins: 40dc7574… / 12cb0bc2… / 121f3e29….

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

## Stage 8: shipped inactive lookup and model indicator

The owned S2 row permutation and literal 64-entry active-row mask table are
bound to the shipped lookup by the universal native gate `inactive-s2-v2`.
It passes in 0.419 s / 146240 KiB with zero swaps in the required scope;
v1's Rust symbol collision is retained as a failed compile and repaired by
renaming only the harness symbols. No shipped source changed.

J10075–10083 establish the source row formula, equality of every literal
table entry, shift/mask bit semantics, and the complete inactive helper result.
`ProverCommitInactiveOutput49.exact_result` returns the canonical zero/one indicator
of the model's `copyInactiveRows` at `rowEquiv.symm j`, for every legal index.
The table proof uses four named groups of sixteen entries after the initial
single expansion hit recursion depth; no limit was raised. J10078 was a
missing-dependency preflight with no compiler started. Failed drafts and exact
successful target/status/wall/RSS/swap/source/dependency/axiom receipts are in
`lean/attempts.json`. Every printed axiom is standard. This finishes raw weight
column zero, not the complete weight constructor or caller composition.

## Stage 9: current full-width power and inverse kernels

J10084–10103 prove current release complex arithmetic, optimized CM31 and
QM31 square, negation, zero testing, complex inverse, QM31 inverse (including
raw-zero rejection), and the complete owned square-and-multiply recursion.
`NativePower49.power` takes arbitrary canonical accumulator/base and every U8
exponent, returning exactly `acc * base^n`; no power-output image is supplied.
`NativeQInverse49.inverse` discharges the norm assertion using the retained
literal field's rootlessness; `reject_zero` covers its other branch.
The native gate `kernel-transitions-v1` passes in 1.111 s / 150712 KiB,
zero swaps, comparing complete operation/operand traces for power iterations
(source U64 cursor <=255 vs owned U8), complex inverse and QM31 inverse.
Primitive arithmetic and zero predicates are separate Lean obligations, not
assumed true by those trace stubs. Only the independent owner is extracted.

J10085 rejects the extractor's inferred i32 shift count; the explicit u32
count in v2 fixes it. A retry with the old receipt name is refused before
launching a tool. J10088 hits the kernel memory limit in `operand_value`
(7170328 KiB); the replacement splits generic wrapping add/sub/mul facts from
the concrete operand graph, and J10089 passes at 4053612 KiB / 1.98 s under
the unchanged cap. Other rejected syntax/cast/decidable-equality drafts and
all receipts are retained. Every accepted theorem prints only standard axioms.
No deployed endpoint premise is removed and no shipped file changed.

## Stage 10: half, final-shift arithmetic caller, Libra column

J10130 identifies the actual half producer with inverse two and proves
`half + half = 1`, without evaluating the fixed inverse chain concretely.
J10138 proves `FinalShift49.exact_result`: the arithmetic caller produces
exactly the shifted polynomial, including actual half construction, source
subtraction and source inverse. Its only denominator condition is the explicit
challenge-not-half condition. The source values of original and eta-term0,
the semantic polynomial, optimized evaluation and the semantic guards remain
caller obligations. This theorem does not assert their provenance.

J10136 proves `Libra49.caller`: actual raw kind four equals the existing model
`SemSource.libraWeight` at every legal coefficient, including both power runs
and the zero suffix. The native complete Libra and half callee-trace gate
passes in 0.800 s / 147808 KiB, zero swaps. Source and owner exponents are
respectively U64 and U8; the gate checks narrowing on every legal branch and
the proved power iteration gate covers all exponents through 255.

J10104 exposes a duplicate extracted M31.ZERO on composing Samples49 with
Interpolate48. Their bodies are byte-identical. Samples49 now imports and
reuses Interpolate48's declaration; no function body changes. J10105/06 check
the new binding; J10108–10129 rebuild every affected retained dependent in
topological order, with snapshots of all overwritten shared sources/objects.
`pins/sample-import-rebuild.json` freezes the schedule. This is a changed
import/dependency regression, not an unchanged replay. Every printed axiom is
standard. The half drafts' small cast proof is replaced by a ZMod.val bound.
Final-shift drafts J10131/33/34/37 hit default heartbeat limits while converting
an inverse-of-two between definitionally equal aliases; the explicit-type
snapshot reveals the mismatch. Aligning the constant's type with Half49 fixes
it (J10138: 3.88 s / 4048524 KiB), without raising any limit. All diagnostics
and source snapshots are retained. No shipped file or deployed premise changed.

## Stage 11: initialized factor reads and seven raw value composition

J10140/43/44 prove the literal TAU table, source coordinate arithmetic and
entire five-row point-factor fill. J10146 binds actual stored matrix reads,
including source shift/mask digits, to the complete factor product. J10150
composes both point and circle initializers with those stored reads/products.
J10148 identifies all seven mathematical raw rows with existing R1
`Batched.ell` on basis vectors, hence their kappa sum with `weightsR1`.
The sums remain symbolic; only the seven functional kinds are split.

J10154/56 compose seven helper values starting from the original alpha array,
including `points.all` and alpha[8]/alpha[9] reads. No statement-point,
factor-value or power-array image is supplied as a premise. Canonicality and
exact inactive/three-point/Libra/two-circle values are conclusions. These are
pure value-composition theorems: they do not assert source call counts for a
reference that recomputes a pure constructor per read. The complete native
outer Weights allocation/layout and reuse, materialized 1024-array, and
higher opening callers remain explicit obligations.

Native gates pass: full arbitrary-context point-row write (3.425 s /
152836 KiB) and complete S2 raw dispatch (3.419 s / 154676 KiB), zero swaps.
The latter checks all seven kinds and legal coefficient indices, including
all five stored multiplications. Primitive inactive and power helpers are
proved separately. Source pins include weights.rs and transport.rs's TAU.
Failed drafts J10141/42/47/49/51/53/55 are retained. In particular, the first
seven-result composition reaches recursion depth; isolating generic storage,
canonicality and map lemmas fixes it without raising any option. Every
accepted printed axiom is standard. No shipped change or deployed-premise
removal. Target not yet established.

## Stage 12: full materialized array and R1 weight-model values

J10157/59/60 prove symbolic ring-map transport of the carry, opening points,
equality/Libra rows and natural-basis evaluator, then identify the complete
WideExact raw rows with R1 `ell`. J10164 proves a complete cell from the actual
raw helpers and kappa producer. J10165/66 prove the full 1024-cell interval
fill, zero initialization and complete kappa-weighted array output. J10168
constructs every raw row from its proved producer and retains every producer
Result as a conclusion (`raw_spec`); `material_model` concludes that each
materialized cell equals existing `Batched.weightsR1`.

The model adapter explicitly retains input representation equations for alpha,
kappa and the four circle coordinates, plus their canonicality. No raw-row,
power, factor, cell or whole-array output identity is a premise. The complete
native outer Weights allocation/layout/reuse and iterator caller still need
composition with these owned value theorems. This is not a native whole-payload
or L2 call-count theorem. The 1024-write gate passes (21.467 s / 614776 KiB,
zero swaps), on arbitrary initial arrays/returned inner-cell values; it checks
only indexed write/context preservation, not inner arithmetic or allocation.
Those have separate retained gates and the named caller boundary remains.

J10158's concrete vector rewrite reaches recursion depth; proving evaluator
and seven-row transport generically first fixes it. J10161's embed alias and
ambiguous E are made explicit. J10162 initially emits a duplicate WideExact.ZERO;
J10163 reuses the identical declaration from Pairs before any dependent is
compiled. J10167's Usize bound is repaired by exposing `size_def`. All failed
sources/diagnostics and accepted section-6 receipts remain. All accepted printed
axioms are standard. No caps/options raised; no shipped files changed.

## Stage 13: complete opening-kernel caller and ordered byte images

J10172/75 identify the entire d/s/t accumulation with the existing R1 round
polynomial, including actual quarter scaling. J10176/79/85 prove the complete
256-entry dual fold and its R1 `dualFold` value. J10180/84 prove the second
round's 256-entry shape via a symbolic padding identity; all legal 64-fibre
reads remain in the live prefix. J10186 identifies the primal cell with R1
`primalFold`. J10187 composes first round, both first folds, second round and
final primal fold. J10188 gives their ordered 7/7/64 coefficient byte images,
using the retained full-width serializer theorem. No supplied round, fold or
byte-image identity is a premise. Inputs are arbitrary canonical batch/weight
arrays and fold challenges; source batch/tape and complete native caller
provenance remain explicit boundaries.

Native full-context dual-array iteration passes in 12.077 s / 567048 KiB,
zero swaps; second-round 256-vs-padded-1024 iteration passes in 7.286 s /
497080 KiB, zero swaps. Full callee operand/order traces are compared. The dual
source pin was corrected from the nearby dense verifier to the actual
prover.rs `fold`, plus weights.rs's quarter, before this stage is committed;
the checked literal Horner body is unchanged.

J10169 is a missing-dependency preflight (RoundPairing's cache module is
R1RoundPairing, reached via BatchedAlgebra); no compiler starts. Rejected
sum/carrier/index drafts J10170/73/74/77/78/81/82/83 are retained. Keeping
`value` and `List.ofFn` opaque, and proving generic Horner/padding facts first,
removes concrete-tower timeouts and list-constructor recursion without raising
limits. All accepted printed axioms are standard. This is a complete owned
opening-kernel value/byte path, not complete native simulator output equality.
No shipped change or deployed-premise removal; no FSExperiments work.

## Stage 14: optimized scalar channels and tower reconstruction

J10189/91/92 prove the owned three-input U64 channel counter, no-overflow
bound, one-reduction dot product, and exact base-field sum. J10194 proves
Karatsuba reconstruction and its linearity over arbitrary finite sums in a
generic quadratic tower. J10195–98 bind the actual three-reduction CM helper,
R multiplication, and complete QM31 reconstruction to that algebra, with
canonical output for arbitrary U64 totals. These results do not yet compose
the native nine-channel component preparation and outer three-input loop.
The prepared-multiplier path also remains open.

Accepted focused targets and resource fields (exit 0, zero swaps throughout):

| Attempt | Exact target | Wall | Peak RSS KiB |
|---|---|---:|---:|
| J10189 | AspisR1ProducerRelease47.Channels49 | 1.25 s | 2612716 |
| J10191 | R1Z.ProverCommitChannelSum49 | 2.22 s | 4061532 |
| J10192 | R1Z.ProverCommitChannelModel49 | 1.82 s | 4038540 |
| J10194 | R1Z.ProverCommitChannelAlgebra49 | 2.30 s | 2437756 |
| J10195 | AspisR1ProducerRelease47.Reconstruction49 | 1.05 s | 2612204 |
| J10196 | R1Z.ProverCommitReconstructC49 | 1.64 s | 4040472 |
| J10197 | R1Z.ProverCommitReconstructQ49 | 1.65 s | 4040640 |
| J10198 | R1Z.ProverCommitReconstructModel49 | 1.66 s | 4031816 |

Source attribution is task base c6be35873ed67abf55956e4e2cac411260bea973
plus each retained source SHA and dependency fingerprint in `lean/attempts.json`.
Every new theorem prints only standard axioms; the two owned-definition
modules contain no new theorem. J10190 and J10193 are rejected simplification
drafts, retained with diagnostics and replaced without increasing limits.

Native gates `channel-v3`, `reconstruction-v1`, and `reconstruct-c-v1` pass
in 1.495/0.862/0.514 s, peak RSS 175408/175792/148512 KiB, zero swaps.
The channel gate uses a bounded product callee, whose arithmetic is separately
proved by the multiplication and channel-bound lemmas. The full reconstruction
caller gate uses the verified CM helper; the separate CM gate checks its body.
These are callee operand/result trace checks, not an L2 operation-count law.
`channel-v1` timed out at 180.003 s (exit 124, cgroup peak 147124224 bytes;
wrapper RSS does not represent all children). `channel-v2` hit the array
memcmp unwind assertion; nine explicit scalar comparisons replace that
comparison in v3, with unchanged unwind/cgroup limits. All failures and exact
source snapshots remain archived. No shipped code was extracted by Aeneas.

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


## Final audit and demonstrated stopping condition

J10199, exact target `R1Z.ProverCommitAudit49`, exits 0 in 1.81 s,
peak RSS 4202656 KiB, zero swaps, under the unchanged 6G/8G/0/64 scope.
Source revision is actual task base
`c6be35873ed67abf55956e4e2cac411260bea973` plus the exact frozen sources
and dependency fingerprints in `pins/final-lean-freeze.json`. Audit source SHA256:
`daab856f3704dbe0baa714be0ce6d853cc02b0025b1cbeaa33c815d380f8728e`.
Its 242 printed results cover all 241 public part-49 theorems and the unchanged
deployed endpoint; all axiom sets are subsets of
`[propext, Classical.choice, Quot.sound]`. Three private theorems were audited
in their original focused targets. All 93 frozen modules import together.
This is an import/axioms audit, not a complete frozen-manifest release replay.

`pins/final-integrity-check.json` confirms current sources match accepted
receipts, endpoint snapshots match the current entire endpoint module,
and all 491 shipped-file hashes match the task base. Main proof sources have
no sorry/admit/axiom/native_decide or raised maximum options. No compiled
binaries, olean, LLBC or archive artifacts are delivered. Diagnostic logs are
retained verbatim, including their original trailing whitespace. Frozen source,
features and toolchain attribution remain in the input pins and host receipts;
no historical proof is reassigned to the earlier 26b922be6 checkout.
No FSExperiments conversion/join, deployed-premise removal, L2 cost closure,
or complete simulator refinement is claimed.

**Stopping obstruction: the authorized J10000–J10199 allocation is exhausted.**
Launcher refusals are explicitly retired, not silently reused. No compile
outside the allocation was attempted. The requested full equality remains
unproved; this is not a mathematical impossibility or a counterexample.
No single completed result is promoted to that equality.

## Exact remaining continuation interfaces

1. Compose actual `qm31_sum_products_small::<3>` component preparation
   (including each CM `a+b` and the outer `c0+c1`), all nine channels across
   three inputs, and the proved reconstruction. Required conclusion: success,
   canonical QM31 output, and decode equal to
   `∑ i : Fin 3, decode (left i) * decode (right i)`, without an assumed
   result/model image. The separate current `PreparedQm31Multiplier::new/mul`
   path still needs its corresponding value proof.
2. Bind the optimized `evaluate_state_only_polynomial` caller for arbitrary
   canonical 28 coefficients and challenge: canonical output, decode equal to
   `(ProverCommitInterpolationPoly48.poly 28 decodecoeff).eval decodea`.
   Current x²/x³/x⁴, scalar/reconstruction, boundary and field kernels are
   available. The seven-block radix-4 owned-loop induction and its source
   transition gate remain.
3. Prove actual semantic oracle success/value from tape columns, sparse
   multilinear evaluation, selected mask, extra constant and terminal value.
   The mathematical oracle target is precisely
   `R0Z.PayloadSplit.maskLinear π B a τ + ch.sem14 *
   terminalValue pub (ch.sem0) (ch.sem1) (ch.sem2) (ch.sem13)
   (zc ch) B (honestClaims (0 : Trace K) a) a`.
   It is not simply `HonestView.oracle τ`. The sparse-equality-weight helper
   needs prefix/trailing-Boolean pruning and selected-mask provenance. Compose
   actual boundary/terminal guard success and running claims, interpolation
   degree facts, and original/eta0 values into the proved final-shift arithmetic.
   `PayloadSplit.rounds` and `originalRounds` remain the exact round targets.
   The source P_R1 good-domain condition (including α9 != half) is not yet
   established for the complete caller.
4. Compose complete `Weights::new` outer allocation, layout, reuse and Vec
   iteration with the proved seven raw producers and full materialized-array
   model theorem. Discharge its explicit α/kappa/circle representation inputs.
   Prove actual source gamma batching of all 1024 coefficients and tape/variant
   coefficient provenance as `coeffsOf AspisR1.rowEquiv τ`.
5. Bind source `sim::encode_at`, `eval_at`, `nodes_for`, `phi_inverse`, and
   opened/folded leaves. Instantiate the existing complete owned opening kernel
   and ordered 7/7/64 byte-stream theorems with those actual canonical batch
   and weight arrays; then compose the whole semantic/opening caller.
6. Final endpoint remains complete native simulator output equal to the
   `R0Z.RefPayload.simE` model payload, namely
   `shift pub B ch (refPayload+ A π B ch (Partition.equiv.symm t))`.
   STOP after that payload equality, before FSExperiments conversion or joins.
   `RustProverRefinement` stays explicit in the deployed theorem until its
   separate obligations are proved. The unchanged verbatim endpoint above
   records that fact, with its original x/rust quantifiers and bound.
