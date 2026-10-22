# Part 48: shipped simulator binding and payload image

**Target not yet established.** Work in progress on
`codex/cx-prover-commit48-20261022`, based on actual worktree revision `617fc58aaf` (D164; a descendant of `26b922be6`).

D164 scope: shipped per-iteration Kani bindings, Lean induction over the owned
loops, then the complete native simulator payload byte image. No Aeneas on
shipped code. No FSExperiments conversion, joins or endpoint changes.

## Stage 1: native evaluator iteration binding

The per-call abstraction records operation tags and every operand, and feeds
arbitrary symbolic results back to both sides at corresponding calls. Equality
of the complete call trace and result establishes a parametric control-flow
binding; it does not prove an arithmetic callee contract. Part 47's separately
checked release arithmetic is reused only at its exact pinned source bodies.
The harness must cover the full 1024/512 array shapes and arbitrary legal
iteration indices; short whole-loop fixtures do not replace this obligation.

## Endpoint before/after

`../../100bit-spend-path-20261013/evidence/prover-commit48-20261022/endpoint/`
contains verbatim complete before/after snapshots, copied from part 47.
They are unchanged. The deployed theorem still requires
`RustProverRefinement`; the D159 L1 obligations remain open.

## Validation and trust

Only attempts J9900–J9999 are allocated to this job. Host compile receipts
will record target, source SHA, dependency fingerprint, exit, wall, peak RSS,
swap, source revision and every printed axiom. Host jobs use MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and the requested linker flags.
No shipped source has changed. The current S4 ELF pins apply to any later
shipped change. No wallet keys, funds, push or merge are involved.

Stage-1 results: `ProverCommitNativePair48.range_finite` / `range_owner`
compose every pair transition, including error/divergence, into the extracted
part-47 owner. `ProverCommitNativeEval48.run_owner`, `raw_value` and `bytes`
compose the nine basis stages, 512 pair steps, normalization and exact cell
image. These are P6 **evaluator denotation** theorems; the native simulator's
coefficient/tape/caller binding is still open. They are not renamed complete
simulator theorems.

Kani `basis_fill_iteration` passes on arbitrary full 512-cell arrays and every
legal `width,j` (84.548 s, 2119456 KiB RSS, zero swaps).
`basis_stage_iteration` passes (0.437 s, 139300 KiB RSS, zero swaps).
`pair_iteration`, using an arbitrary current iterator cursor and the full
1024/512 arrays, passes (14.261 s, 717272 KiB RSS, zero swaps).
All compare complete callee traces and returned state with universal symbolic
callee results; no arithmetic law is inferred from those stubs.

Failed drafts: pair v1 has an insufficient unwind bound in its test-input
`array.map` (20.502 s, no verified result). v2 times out at 180 s while replaying
that construction. v3 removes the map via a transparent representation but
still replays the iterator prefix; it is stopped without a verdict. The
replacement v4 starts at the current cursor under the explicit pure std
semantics below. No memory cap increase or unchanged retry is used.
`basis-stage-v1` is a reservation refusal before any command, not a compile.
J9900 fails on pair-pattern eta conversion; J9901 fixes it. J9901–J9903 pass,
with only standard axioms (J9903's first two theorems are axiom-free).

D157 fields added, in `ProverCommitIteratorStd48.TrustedStd`:
`slice_chunks_exact` (complete forward chunks, remainder omitted) and
`iterator_zip` (forward lockstep traversal until either input is exhausted).
Call site: `crates/aspis-core/src/r0/encoder.rs`, `eval_pair`'s
`q.chunks_exact(2).zip(basis)`. The fields concern only documented pure std
semantics, and have a proved mathematical consistency instance. They do not
assert arithmetic correctness, callback success, allocation totality,
simulator equality, or privacy. The iterator model and its count theorem
are separate from the kernel-checked evaluator induction; the remaining
source/P6 composition is stated explicitly rather than hidden as an axiom.

## Stage 2: aggregate y1 and full-width arithmetic

J9905 proves `ProverCommitY1Aggregate48.every_lane`: all 29 normalized native
evaluator-denotation calls succeed, in order, with their canonical exact
values, and the concatenated 928 bytes equal the corresponding model list.
It uses symbolic list induction and pointwise byte congruence. This replaces
the part-47 abandoned aggregation without recurrence expansion or a larger
resource limit. J9904's only failure is a final natural-number scalar notation
conversion in the byte-count lemma; it supplies no accepted theorem.

The following opening fields use arbitrary full WideExact challenges, so the
subfield-only arithmetic of part 47 is insufficient for them. J9907 proves
canonical QM31 operations and raw multiplication by the tower constant;
J9909 gives its exact decoded value; J9910 proves actual release full-width
WideExact add/mul preserve canonicality and have the exact tower value.
`ProverCommitWideOps48.mul_exact` has no checked-success, high-half-zero,
source-success, or callee-equality premise. The checked/release relation is
reused only after the checked canonical result has been established.
These close arithmetic obligations, not the semantic/interpolation caller
or complete simulator output equality. J9906 is a redundant-tactic draft;
J9908 is a rejected ambiguous-carrier draft. Their original diagnostics and
nonaccepted axiom output remain in the receipts.

J9911 proves the full canonical source limb tuple has the exact full-width
32-byte image and decoding. The actual native serializer also passes Kani on
arbitrary canonical low and high coordinates (2.674 s, 294936 KiB RSS, zero
swaps). Kani also checks the raw-M31 trait embedding chain agrees with the
semantic column lift followed by `from_qm31` (0.461 s, 158976 KiB RSS, zero
swaps). The copied field files are byte-identical to their current shipped
sources; `pins/wide-body-inputs.json` records both complete files and the
scalar-trait source pin.

## Stage 3: opening coefficient mix and fold owners

The new counter owners in `opening-owner/lib.rs` translate successfully.
Only those owned counters go through Charon/Aeneas; no shipped loop is
extracted. Their reused arithmetic declaration bodies are compared byte for
byte by `harness/bind-opening.py` before the new extracted owner definitions
are installed as `AspisR1ProducerRelease47.Opening48` (J9912).

The actual opening's coefficient-fold expression passes its arbitrary-lane
and arbitrary-coefficient-index Kani transition (5.381 s, 387972 KiB RSS,
zero swaps). The source primal fold-cell expression passes its complete
callee-trace gate (0.872 s, 167704 KiB RSS, zero swaps).
J9913 proves the **entire 29-lane coefficient mix**, with full-width
canonical inputs and exact decoded weighted sum. This is not a theorem that
the source gamma-power producer or source coefficient arrays have already
been identified with the full model trace. Those producer bindings remain
explicit work, as do the fold-array value induction and remaining semantic
and opening fields.

## Stage 4: complete primal folds, powers, and initializer boundary

J9917 / J9921 prove both counter owners' finite denotation and the generic
interval value invariant. J9929 composes all 256 first-fold and 64 second-fold
cells and proves each full-width final cell's exact 32-byte image, in
`ProverCommitFoldOutput48.fin_bytes`. The input mixed coefficients still have
to be composed with the actual native coefficient/mix caller and the retained
R1 batched payload. This is a fold-kernel image, not the complete model payload.

The power owner translates without external templates. `bind-powers.py`
compares reused field bodies and records the nominal `fill` → `power_fill`
rename, avoiding a collision with the existing basis owner. Native gamma and
kappa transition checks pass (2.325 / 1.129 s, 172024 / 172488 KiB RSS, zero
swaps), including the last iteration's return without another multiplication.
J9925 proves the entire owned counter by symbolic array update induction;
J9928 proves both complete source-owner power arrays equal the exact field
powers, for arbitrary full-width canonical input. No power-array or
callee-success hypothesis is supplied. J9918–J9919 and J9922–J9924 are
rejected syntax, carrier-resolution, and let-pattern drafts; J9926 has an
unresolved final conditional rewrite. They are not accepted proof evidence.
J9927 is a dependency-preflight refusal, with no compiler attempt, because
J9926 had failed. Its proposed input is retained; its number is retired.

`Weights::new` uses unsafe partial initialization, outside D157's pure-std
permission. Its literal constructor body is therefore checked directly with
full native QM31-shaped fields, arbitrary canonical arithmetic results and
arbitrary canonical statement-point helper output. All initialized fields
are read and checked, and variant/points/extras are preserved. This focused
Kani gate passes (28.034 s, 2016128 KiB RSS, zero swaps). It supplies no
weight-value/model equality, allocation-totality, or privacy claim. Its first
invocation is a compiler rejection because the stubbing flag was absent;
the replacement enables that feature without changing or raising resource
limits. No unsafe std law is added.

A native fixed-inverse-chain context gate also passes (0.954 s, 138244 KiB
RSS, zero swaps) with the raw-zero assertion retained. This is only the
callee-trace context gate. The retained S7 inverse theorem and its immediate
helper objects are absent from the shared env-J cache; no complete inverse
source binding or interpolation certificate is attributed to this check.

## Stage 5: direct semantic arithmetic, inverse binding, and extras

J9931 checks a focused copy of the retained S7 fixed-inverse algebra against
the current release multiplier, avoiding its unrelated geometry imports and
missing cache objects. The native chain context and square iteration gates
pass (0.954 / 0.767 s, 138244 / 136604 KiB RSS, zero swaps). The raw-zero
assertion and its Result failure are retained. The resulting
`ProverCommitInverse48.inverse_exact` / `inverse_canonical` establish the
source-owner fixed chain's exact inverse and output range. This does not
identify the semantic interpolator or prove its denominators nonzero.
J9930 is a rejected missing-namespace-import draft, not accepted evidence.

J9932 checks direct canonical release QM31 add/mul/sub, without requiring an
embedded WideExact carrier. The source reverse-Horner transition for
`host_semantic::extra` passes on arbitrary legal side/index and full 1024-cell
coefficient arrays (1.336 s, 175460 KiB RSS, zero swaps). The recursive owner
translates; reused field declarations are body-identical (J9933). J9935 proves
both complete 28-coefficient polynomials have their exact field values.
J9934's fixed-size array proof initially exceeds the default recursion depth;
it is replaced with the named `List.length_ofFn` lemma, not a raised limit.
The other rejected draft is an unresolved final zero/literal rewrite.

D157's additional pure std fields, in
`ProverCommitIteratorConsumer48.TrustedStd`, are `iterator_rev`,
`iterator_fold`, and `iterator_flat_map`. Call sites are
`host_semantic.rs::extra` (`iter().rev().fold`) and
`prover.rs::encoded` (`into_iter().flat_map(...).collect`). The fields state
only ordered list reversal, left fold, and flatten-after-map. No callback
arithmetic, field image, source success, allocator totality or privacy law is
included. J9936 proves the consistency instance and consumer transports
without axioms.

J9937 composes the actual power owner and all 29 coefficient-mix iterations:
`ProverCommitBatchMix48.value_exact` gives the exact gamma-weighted sum,
without a supplied power-array identity. This is still a coefficient-cell
producer theorem, not the missing whole simulator source-to-model instance.

## Stage 6: interpolation reference and focused primitive checks

The first structurally recursive interpolation reference fails in Aeneas at
its conditional predecessor read (`lib.rs:25`, `InterpBorrows.ml:2731`). It
contains no shipped loops, iterators, maps or timing. The replacement isolates
the predecessor read in an owned scalar helper; that helper translates on
its own, and the changed complete owner then translates. The original failure
and source are retained. This is a source change and focused preflight, not
an unchanged retry or a source-side Aeneas run.

J9938 checks the resulting owner definitions after every reused arithmetic
body (including inline-attributed constants) is compared with the retained
release declarations. J9939 proves the coordinate scalar reference exactly
multiplies the decoded QM31 by the decoded base-field word and always returns
canonical limbs. Its native `QM31::mul_m31` callee-trace binding also passes
(0.504 s, 172936 KiB RSS, zero swaps). J9940 checks the exact canonical
M31 add/sub/mul contracts needed by interpolation. J9942 checks the array and
predecessor primitives; J9945 proves the complete descending coefficient-update
invariant. The native basis-step gate passes (1.882 s, 170832 KiB RSS, zero
swaps). J9941 / J9943 / J9944 are rejected import, literal, and monadic-let
rewrite drafts, all retained separately.

The Lagrange factor/denominator invariants, complete interpolation value,
semantic round sums/guards, remaining weight/round/opened-leaf images, and
the complete native simulator payload equality are not yet established.
No callee-equality or model-image law is postulated to skip them.

J9947 proves the arbitrary-size polynomial coefficient and multiplication
shape lemmas. J9949 identifies the separately extracted inverse and square
counters with the proved release fixed chain, including raw-zero Result
failure. J9950 composes the descending update with the polynomial shape law:
the source owner multiplies by X-j and preserves the required upper-zero
region. These are generic lemmas for the next denominator/factor induction;
they are not a complete interpolation or native payload theorem. J9946 and
J9948 are rejected conditional/Decidable-instance rewrite drafts.

All shipped files are unchanged relative to the actual D164 worktree base
`617fc58aaf`; this is the comparison used for the shipped-file rule. The
user-mentioned `26b922be6` is an earlier ancestor with intervening shipped
changes already present before this task. No ELF rebuild is triggered by this
worker's changes; no stale ELF pins are adopted. The current S4 pins remain
40dc7574… / 12cb0bc2… / 121f3e29….

## Stage 7: omitted-node product and source initialization

`InterpolationSchedule48` proves the exact skipped-node degree schedule,
polynomial/denominator products, their evaluation identity, and nonzero
M31 denominators for the 28 distinct nodes. `InterpolationFactors48`
propagates these invariants through the entire owned factor loop.
`InterpolationInitial48.prepare_exact` closes the actual zero-array/one-cell
initialization and all 27 selected factors, including the nonzero raw-word
condition consumed by the inverse. `QArray48` supplies symbolic QM31 array
index/update and zero initialization for the next accumulator proof.

Accepted focused attempts: J9952 schedule, J9955 indices, J9958 factors,
J9960 QM31 arrays and J9961 initialization. All print only the standard
axioms; exact timing, RSS, zero swap and source/dependency fingerprints
are in the attempt receipts. J9951/53/56/57/59 are failed local theorem
iterations, retained as diagnostics. J9954 did not launch a compiler because
the preceding dependency had failed; its number is retired. No full
manifest replay or shipped-source extraction was performed. The full
interpolator and simulator payload image remain open.

## Stage 8: complete owned interpolation output

`InterpolationAccumulate48.accumulate_value` proves every selected coefficient
update and canonicality for an arbitrary interval. `InterpolationRow48.row_value`
composes the initialized factors, nonzero denominator, exact inverse and scalar
multiplication into the normalized omitted-node polynomial contribution.
`InterpolationOutput48.interpolate_value` then composes all 28 source-owner
rows, for arbitrary raw QM31 input words, into the explicit interpolation sum.
This closes the complete owned interpolator's value/canonicality law, not the
native simulator caller or complete payload law. The bridge to the standard
`Lagrange.interpolate` definition is the next focused target.

Kani `outer_interpolation::proofs::factor_iteration` checks the literal native
selected-node body against the owned descending-counter body for every legal
node and degree, including skip behavior and every primitive operand/result
trace: exit 0, wall 115.403 s, peak RSS 1039104 KiB, swaps 0. Its only control
rewrite is `continue` to returning the unchanged iteration state, documented
with source/body hashes. `accumulator_iteration` checks the literal native
coefficient update against the owned update: exit 0, wall 3.487 s, peak RSS
298204 KiB, swaps 0. All native field operations remain universal callee
results here; their exact arithmetic contracts are separately proved.

Accepted J9963 accumulator, J9964 embedding, J9966 complete row and J9975
complete interpolator print only standard axioms. J9962 lacked an explicit
array import; J9965 was the initial row bridge; J9967–J9974 isolate monadic
pair destructuring/association in the outer loop. Their diagnostics are
retained. The successful bridge uses the proved initializer/factor Result,
then an explicit monadic expression; no options, assumptions or caps changed.

## Stage 9: standard interpolation model and byte image

J9977 proves the symbolic normalized omitted-node product equals the standard
Lagrange basis for every node; J9980 composes this with all source-owner rows.
`InterpolationModel48.interpolate_model` returns canonical coefficients and
an equality to `Lagrange.interpolate Finset.univ` on nodes 0–27 for arbitrary
raw input words. It contains no supplied coefficient/model-image identity.
J9982 proves every coefficient's embedded 32-byte image, the complete ordered
896-byte payload image, and its length. This is the **unshifted owned
interpolator output**, not a native semantic-round theorem: source sample
provenance, boundary guards, final shift and native caller composition remain.
J9976/78/79/81 are retained focused drafts; J9981's length proof attempted
excess reduction and hit the default heartbeat limit. The replacement keeps
the output/model cells opaque and proves only list shape; no cap was raised.

The next opening helpers are separately extracted from `batched-owner`, with
no shipped-code extraction. J9983 checks the rebound owner declarations.
J9985 proves the actual WideExact scalar source operation on arbitrary raw
low/high words, including the scalar's `% P` normalization; outputs are
canonical. J9986 proves the dual fold cell's exact reverse-order polynomial
and quarter scaling. These do not discharge the complete weight producer,
materialization, round/fold callers, or simulator payload equality.

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
