# Part 50: native simulator continuation

**Target not yet established.** Branch `codex/cx-prover-commit50-20261022`.
Authorized Lean budget: J10200–J10299 only. Work proceeds through the six
interfaces in part 49, stopping at native payload equality, before any
FSExperiments conversion or joins.

## Frozen inputs and scope

Task base is recorded in `evidence/prover-commit50-20261022/pins/revision.txt`
under `docs/research/100bit-spend-path-20261013/`. No shipped file is changed.
Retained release ELF pins: default 40dc7574…, devnet 12cb0bc2…, Pool 121f3e29….
No fresh ELF build is claimed. Shipped code is never extracted by Aeneas;
independent owners and native transition gates provide the binding route.

## Endpoint before/after

The entire deployed endpoint is preserved verbatim in `endpoint/before.lean.txt`
and `endpoint/after.lean.txt` in this task's evidence. The snapshots are identical.
`RustProverRefinement` remains an explicit premise, with unchanged x/rust
quantifiers, failure event, conclusion and bound. No premise removal is claimed.

## Validation

Focused Lean targets run only on the build host, one module per attempt.
All host tools use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
Rust uses four jobs, release optimization, and
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'`.
Exact source hashes, dependency fingerprints, target/status/wall/RSS/swaps,
source attribution and printed axioms are retained per attempt.

## Stage 1: component preparation and complete three-product value

J10203 proves `Prepare50.q`: all nine prepared coordinates are canonical and
are precisely the symbolic tower components, including CM `a+b` and QM
`c0+c1`. J10206 proves every entire three-input scalar accumulation and the
complete nine-total matrix. J10209 proves `Dot50.exact_result`: the independent
owned caller succeeds, returns canonical QM31, and decodes to
`∑ i : Fin 3, decode (x i.val) * decode (y i.val)` for arbitrary canonical inputs.
No prepared-coordinate, accumulator, or output/model identity is a premise.

Native preparation and all-27-product aggregation gates pass, with complete
output matrices; preparation also checks paired arithmetic operands and order.
The aggregation products are arbitrary bounded callee answers. Their integer
multiplication and canonical bound are separately proved by the retained
`NativeSquare49.mul64` and `ChannelSum49.product_bound`. This composes retained
part-49 channel transition/reconstruction gates with the new value proof;
it does not prove equality of the reordered complete caller's timing trace.
The prepared-multiplier path needed by the next interface remains next work.

J10200 was refused before compilation by the copied launcher's old range guard;
it is retired. The launcher now accepts only J10200–J10299 and retains global
Lean serialization and the 6G/8G/0/64 caps. J10202/05/08 are rejected carrier,
array-size inference and literal-index drafts; their replacement sources pass.
All accepted axioms are subsets of `[propext, Classical.choice, Quot.sound]`.
Focused receipts in `lean/attempts.json` record exact source attribution,
source/dependency fingerprints, target/status/time/RSS/swaps and axiom lines.
No shipped file changed; no deployed endpoint premise is removed.

## Stage 2: prepared multiplier and optimized evaluator

J10212 proves the full prepared constructor/multiply value path. Its row-input
representation premise is discharged by `caller`; canonical inputs suffice for
canonical output decoding to their product. The verbatim native constructor
and multiplication gate passes in 2.699 s / 213116 KiB, zero swaps, with exact
operation/operand traces for arbitrary matrices/RHS and universal paired
arithmetic answers. No prepared-output/model identity is assumed.

J10239 proves `ProverCommitEval50.exact_result`: the complete owned optimized
28-coefficient evaluator returns a canonical QM31 decoding to
`(ProverCommitInterpolationPoly48.poly 28 decodecoeff).eval decodea`.
It includes actual x²/x³/x⁴ construction, the three-product block, prepared
constructor/multiplication, and all six reverse iterations after block six.
J10213/24/29 prove generic polynomial grouping before tower specialization;
J10237/38 prove the final block and loop. The native complete seven-block
caller gate passes in 4.944 s / 266592 KiB, zero swaps. It compares all callee
operands and order on arbitrary full coefficients. Prepared storage is an
opaque handle in that caller gate; its full matrix interface has the separate
prepared gate. No arithmetic law is inferred from universal callee stubs.

Initial index drafts confused the `core.num` and `Std` wrapper names; explicit
wrapping/index equations fix them. J10217 is a retired missing-dependency
preflight, no compiler launched. The final concrete bridge initially hits the
default heartbeat limit. Its explicit-type diagnostic (J10232) identifies
powers elaborated over two definitionally equal field aliases with different
instance paths. Using the decoder's exact carrier in both block/loop binders,
and a generic Field bridge, fixes this. Both changed modules are recompiled
before their consumer; no old dependent is silently reused. J10239 exits 0 in
1.97 s / 4054204 KiB, zero swaps. Failed sources/diagnostics are retained;
no option/cap was raised. The rejected concrete helper is retained only in
attempt snapshots, not the deliverable proof tree.
All accepted printed axioms are standard. No pure std trust field or shipped
source was changed. The complete semantic oracle and later interfaces remain.

## Stage 3a: sparse equality factors, rows and complete weighted sum

The generic pruning identities prove Boolean suffixes remove exactly zero
weights. `SparseRows50.row` identifies arbitrary source MSB-first rows with
existing model `eqWeight (toR0 p)`. `SparseConcat50`/`SparseEnum50` prove the
actual prefix·2^trailing+suffix row enumeration is bijective, with the exact
appended bit vector, and prove dense-to-sparse weighted-sum equality without
expanding a Boolean cube. J10261 audits these enumeration/pruning results.

J10247 proves the actual source bit-shift/mask condition and canonical factor;
J10249/54 prove the entire owned prefix product equals its mathematical weight.
J10255 proves source shift/or assembly, its exact natural value and <1024 bound.
J10260 proves the complete owned ordered sparse weighted-column sum, including
every generated weight, selected array read and field operation. Canonical
point/column inputs and public bounds suffice; no weight-array/sum image is a
premise. Scanner/suffix provenance and the link to complete native MLE remain.

Native gates: sparse-factor transition 0.904 s / 163524 KiB; row assembly
0.312 s / 141428 KiB; full 1024-column weighted-read transition 65.127 s /
3415572 KiB; all exit 0, zero swaps. The first factor harness failed because
its own precondition added unconstrained usize values before constraining
bounds; constraining those values first fixes the harness. No source defect
is inferred from that rejected harness. The first sparse owner extraction
fails in Aeneas borrow merging; a separate factor helper fixes it. A stale
previous extraction reached the binder after that failure; J10243 is refused
before compilation, retired, and the binder now checks expected declarations.
Later extraction outputs use distinct version directories. A missing brace
in the first sum-owner draft is retained as a Rust compile failure, then fixed.
All Lean failures, source/dependency fingerprints and resource receipts remain;
accepted axiom sets are standard. No shipped file or new TrustedStd field changed.

## Stage 3b: trailing scanner, suffix provenance and owned MLE caller

J10265 proves the actual raw zero/one predicates and their canonical decode
laws. J10267 proves the complete reverse scanner, including the returned
prefix width, every Boolean suffix coordinate, and the maximality boundary.
J10268 identifies the entire source-owned suffix encoding with existing
`R0P.rowCode`; J10271 proves the actual count and caller parameters, including
all bounds and decoded suffix bits. J10272 proves `Mle50.model_result`: the
complete owned sparse MLE succeeds, is canonical, and equals the existing
`dot (eqWeight (toR0 p)) column`, for arbitrary canonical point/column inputs.
No scanner width, suffix value, weight array or output/model image is assumed.

The full native `iter().rev().take_while(...).count()` and slice suffix loop
are checked directly by Kani against the recursive owners on arbitrary full
raw QM31 arrays. Gate exit 0, 6.970 s, 795760 KiB, zero swaps. This is paired
with the prefix/row/weighted-read gates already recorded. Source Vec emission
and iterator caller assembly still need their explicit composition; the owned
MLE theorem is not promoted to whole native semantic-oracle success. No
TrustedStd field is added. J10272 exits 0 in 1.72 s, peak 4046620 KiB, zero
swaps, standard axioms only. Rejected parser, scalar and dependent-index drafts
are retained with their replacements. Shipped files remain unchanged.

## Stage 3c: selected-mask arithmetic kernels and symbolic coefficient inventory

J10283 proves the actual optimized two linear forms equal model `maskLinear 0`
and `maskLinear 16`, starting with canonical point inputs. The full reverse
statistic counter and raw four-limb scaling are proved separately. The complete
power-26 chain returns a canonical result with the exact power value. The native
linear/power gate passes in 1.753 s / 179320 KiB, zero swaps. J10285 proves the
complete prepared Horner evaluator of 27 arbitrary canonical coefficients;
its native full-context gate passes in 2.651 s / 259776 KiB, zero swaps.

J10289 proves all four optimized tower-basis operations, with canonical output
and exact value. The first owned Rust scalar `match` extracts to a Lean pattern
that selects the panic fallback at literal zero; that rejected declaration and
proof draft are retained. Replacing only the independent owner's match by
scalar tests gives the correctly bounded dispatch; J10288/89 pass. No shipped
source is edited. Native tower v2 checks this exact if-dispatch against the
shipped usize match, including full output/operand traces, in 0.728 s /
164616 KiB, zero swaps. J10292 adapts the helper to `Mask.mulTowerBasis`, retaining
only the two explicit input equations for B.i and B.u; their complete caller
instantiation remains open.

J10294/95 prove the symbolic selected-mask polynomial inventory, exact zero at
omitted exponent 23, the zero suffix above degree 26, reconstruction from its
27 mathematical coefficients, and evaluation equal to the model mask value.
These do not assert that the actual source coefficient-array producer has
those values. J10297 proves the actual final shared + (1+L16^26)*g arithmetic;
its native paired-callee gate passes in 0.431 s / 148196 KiB, zero swaps.
All accepted theorem axiom sets are standard. No TrustedStd field is added.

**Rejected final composition (J10298).** The attempted arithmetic caller retains
a named input coefficient law for the unproved 26-write producer. Its concrete
kernel check hits the unchanged 7,000 MiB limit: exit 1, wall 19.10 s, peak
7170376 KiB, zero swaps. The source and diagnostics are archived in the attempt
receipts. It is removed from the accepted proof tree, not rerun and not given
a larger cap. The printed self-reference in that failed declaration is not an
accepted axiom or proof. No claim is made that even this conditional caller
composition compiled. Next: isolate the concrete term/instance reduction,
keep the caller arithmetic abstract, then discharge the actual coefficient
producer law before claiming complete selected-mask success.

## Verbatim deployed endpoint before/after: unchanged

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

## Final audit: FAILED; budget exhausted

J10299, exact target `R1Z.ProverCommitAudit50`, fails at imports: exit 1,
wall 0.95 s, peak RSS 3246284 KiB, zero swaps. The exact diagnostic is:

```
import AspisR1ProducerRelease47.Linear50 failed, environment already contains 'AspisR1ProducerRelease47.field.QM31.mul_m31' from AspisR1ProducerRelease47.Batched48
```

No `#print axioms` command in this final audit executes. The failed audit
source is preserved verbatim as
`lean/sources/attempt-10299-ProverCommitAudit50.lean.txt` in the evidence;
it is not retained as an accepted module in the proof tree. Audit source
SHA256: `40874c72f2f2e2c38086bbf02c5ef6c551b3bd24ab397661eb01f02f1f51f92f`.
The audit source revision is `7ea294e32bf10d02b9b8ec34b9631678a367337e`, plus its
frozen source/dependency fingerprints. Actual task base is
`3b95419ce01a5709a7cd19d71c794cf815999041`, not an attribution of these new
results to the earlier research revision quoted in the prompt.

Static inspection confirms **both** `field.CM31.mul_m31` and
`field.QM31.mul_m31` are byte-identical between `Linear50` and retained
`Batched48`. `pins/integration-collision.json` records both declaration hashes
and the exact repair/rebuild schedule. Next continuation must import/reuse
those two declarations from `Batched48` in `Linear50`, remove the duplicates,
and rebuild these six affected targets in order:

1. `AspisR1ProducerRelease47.Linear50`
2. `R1Z.ProverCommitScale50`
3. `R1Z.ProverCommitLinearLoop50`
4. `R1Z.ProverCommitLinear50`
5. `AspisR1ProducerRelease47.MaskFinish50`
6. `R1Z.ProverCommitMaskFinish50`

Then repeat the integration audit with new authorized numbers. No uncompiled
source repair is installed after this allocation ends. The failed J10298
concrete arithmetic caller also needs reduction-shape isolation; it must not
be rerun unchanged or with a larger cap.

`pins/final-lean-freeze.json` freezes 52 individually accepted focused modules
and 91 public theorem statements. Their original focused `#print axioms`
results are all subsets of `[propext, Classical.choice, Quot.sound]`. This is
**not** a successful combined import/axioms audit: no claim that these results
currently compose with the entire retained part-49 cone is made. There is no
complete frozen-manifest release replay or security closure claim.

`pins/final-integrity-check.json` accounts for all 100 numbers: 97 compiler
attempts (56 successful) and three retired preflight refusals (10200, 10217,
10243). It verifies accepted source hashes and receipts, unchanged endpoint
snapshots, no forbidden proof escapes or raised maximum options, no binary/
olean/LLBC/archive delivery, and all 491 shipped files unchanged from task base.
The ELF rebuild rule was not triggered. Retained pins remain default
40dc7574… / devnet 12cb0bc2… / Pool 121f3e29…; no fresh ELF rebuild is claimed.

**Stopping condition: J10200–J10299 is exhausted.** In addition, J10299 exposes
a concrete integration collision and J10298 a concrete kernel resource failure.
Neither is a counterexample to the desired simulator equality. No further
compile was launched, and no historical proof is reassigned to this new cone.

## Exact remaining continuation interfaces

1. The new three-product arithmetic and optimized evaluator have focused owned
   value proofs and native gates. Integrate the cone after the duplicate-declaration
   repair above; do not promote those local results to whole simulator refinement.
2. Finish semantic source provenance: source Vec emission/iteration into the
   sparse MLE; actual tape columns and statement-point claims; actual selected
   coefficient-array writes (including the zero cell at exponent 23); model-basis
   instantiation; semantic terminal and extra/original/eta0 values. Compose
   sample sums, interpolation and optimized evaluation into the exact
   `PayloadSplit.rounds`/`originalRounds` targets and prove boundary/terminal
   guard success. Establish the source P_R1 good-domain condition, including
   alpha[9] != half. The exact oracle target remains
   `R0Z.PayloadSplit.maskLinear π B a τ + ch.sem14 * terminalValue pub
   (ch.sem0) (ch.sem1) (ch.sem2) (ch.sem13) (zc ch) B
   (honestClaims (0 : Trace K) a) a`.
3. Then interface 4: complete `Weights::new` allocation/layout/reuse/iteration,
   its input representation laws, gamma batching of all 1024 coefficients and
   tape/variant provenance as `coeffsOf AspisR1.rowEquiv τ`.
4. Then interface 5: actual source `encode_at`, `eval_at`, `nodes_for`,
   `phi_inverse`, opened/folded leaves and semantic/opening caller composition.
5. Final endpoint is still complete native simulator payload equal to
   `shift pub B ch (refPayload+ A π B ch (Partition.equiv.symm t))`, the
   `R0Z.RefPayload.simE` payload. It is unproved. Interfaces 4–6 were not reached
   within this allocation. STOP there before FSExperiments conversion or joins.

`RustProverRefinement` remains explicit in the unchanged deployed theorem;
no premise, quantifier, failure event, metric, conclusion or bound is weakened.
**Target not yet established.**
