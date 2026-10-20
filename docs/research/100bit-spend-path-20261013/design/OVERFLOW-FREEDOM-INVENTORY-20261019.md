# Overflow-freedom inventory, stage-1 arithmetic cones (R22, route (a)), 2026-10-19

Branch `codex/r1-overflow-free-20261019`, base `f9016d0a2`. Gap-map row R22
(`design/LEAD-NOTE-SOUNDNESS-GAP-MAP-20261019.md`, addendum).

## 1. What has to be shown

R22 needs total checked execution on admitted inputs, not an implication
from successful checked execution. For a `Result (RustResult α ε)`, an ordinary
`ok (Err ε)` is allowed: rejecting malformed input is not integer overflow.
Bounds below are premises unless the cited caller theorem derives them.
Explicit `wrapping_*` and Rust `as` casts are total in Aeneas; they must be
inventoried, but must not be confused with failure-capable `Scalar.add` etc.
Array/slice failures are recorded separately from arithmetic overflow.

Handover review: `93f5025d9` adds only this skeleton and four helper files;
there is no predecessor Lean proof or compile receipt to trust. The actual
pre-handover base is `f9016d0a2`, not the historical common-rules base.

## 2. Extractions used

Authoritative focused emitted inputs (all paths relative to this research directory):

- `lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean`
  (semantic polynomial arithmetic and copied field kernels).
- `lean/extracted-source-proof-loops-20261019/AspisR1BatchedWeightsExtraction/Funs.lean`
  (selected `push`/`value`, not the whole verifier caller).
- `lean/extracted-decode-k-canonicality-20261018/AspisR1DecodeKFullV10/Funs.lean`
  (strict decoder including checked size guards).
- `lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean`
  plus `lean/bridge-prepared-3335-20261016/ExtractedPreparedModel.lean` and
  `lean/ExtractedSemanticRoundsModel.lean`: the models retain explicit child
  boundaries; their successful-execution reachability theorems are not
  no-overflow theorems for those boundaries.

The operation census in the evidence directory pins each input hash and source
line. It is a lexical aid, not a verified call-graph or type inference tool.
Historical V5 sources under `aeneas-verif/` do not establish current R1 bodies.
Gap-map R1/R2/R5 and S1–S9 explicitly distinguish the current source frontier.

## 3. Inventory by function (extracted cones)

Notation: `P=2^31-1`, `C=(P-1)^2`, `B=2^34`, `W=Usize.max`.
All canonical field limbs are `<P`. An entry describing several lanes applies
to each literal lane in the census. `Usize` is target-parametric; all fixed
stage-1 counts below fit even a 32-bit target.

### Field leaves (SemanticCallExtraction, lines 25–183)

| Function | All local integer/index sites | Sufficient bound; output |
|---|---|---|
| `field.reduce_u64` | U64 `>>>31` twice, U64 add twice, U32 guarded subtraction; casts U32→U64 and U64→U32 | shift count 31<64; first fold ≤10737418238; second ≤P+4; guarded subtraction nonnegative; output <P. Casts are total, not checked failures. No input restriction beyond stored U64. |
| `M31.reduce_u64` | delegates reducer | all U64; canonical output |
| `M31.add` | U32 add and guarded sub P | sum ≤2P-2<2^32; subtraction only if sum≥P; output <P |
| `M31.sub` | U32 `self+P`, subtract rhs, guarded sub P | self+P≤2P-1<2^32; rhs<P≤self+P; output <P |
| `M31.mul` | total widening casts; U64 product; reducer | even stored U32 product ≤(2^32-1)^2<2^64; output <P |
| `M31.double` | `M31.add self self` | canonical input; canonical output |
| `CM31.add/sub` | two M31 calls | both inputs canonical; canonical output |
| `CM31.mul` | two widened U64 sums and their U64 product; M31 mul/add/sub and reducer | sums≤2P-2; cross product≤(2P-2)^2<2^64; canonical output |
| `mul_by_r` | M31 mul/add/sub calls | canonical CM31 input; canonical output |
| `QM31.add/mul` | CM31 add/sub/mul, mul_by_r calls | canonical inputs; canonical output |

### Semantic polynomial bodies (same emission, lines 191–288)

| Function | All sites | Invariant |
|---|---|---|
| `semantic_boundary_loop.body` | polynomial Usize index; QM31 add; Usize `index+1` | guard index<28; therefore index+1≤28≤W; polynomial and accumulator canonical |
| `semantic_boundary_loop` | Aeneas loop, no extra scalar operation | decreasing `28-index`, index≤28; same canonical invariant |
| `semantic_boundary` | polynomial[0]; boundary loop seed index 0 | fixed 28-element array; all coefficients canonical |
| `semantic_value_loop.body` | Usize `index-1`; alpha[round]; QM31 mul; polynomial[index-1]; QM31 add | guard index>0, index≤28, round<10; all operands canonical |
| `semantic_value_loop` | Aeneas loop | decreasing index, index≤28 |
| `semantic_value` | calls value loop at index 28, canonical zero seed | canonical polynomial/selected alpha, round<10 |
| `*_entry` | wrapper only | same child premises |

### Batched rho (BatchedWeightsExtraction, lines 25–180)

| Function | All sites | Invariant |
|---|---|---|
| `field.reduce_u64`, `M31.reduce_u64` | same reducer sites above | unrestricted stored U64 |
| `push_loop.body` | iterator next; limbs[j]; total U32→U64 conversions; U64 multiply; Vec mutable index; old[j]; U64 addition; array update | j<4; index<raw.length; canonical power limb and basis; old lane `<B+(terms%4)*C`; product≤C; total `<B+4C<2^64` |
| `push_loop` | Aeneas loop over 0..4 | checked iterator successor only while j<4; no other scalar site |
| `push` | call push_loop; total `terms & 3`; Vec read/mutable index; lanes[0..3]; four U64 shifts by 31; four U64 adds | same index/canonical/phase premises; fold of every stored U64 is <B. `push` does **not** increment terms; caller cadence remains an obligation. |
| `value` | Vec index; lane[0..3]; four reducers; four indexes of freshly made array | index<raw.length, literal lanes<4; unrestricted stored U64; canonical QM31 output |
| `push_entry/value_entry` | child call only | same premises; no hidden counter increment |

### Strict field and indexed decoders (DecodeKFullV10)

| Function | All sites | Invariant |
|---|---|---|
| `M31.from_le_bytes` | total U32 byte conversion and comparison | fixed four-byte array, no failing scalar op; success gives <P |
| `CM31.from_le_bytes` | slice ranges 0..4 and 4..8; array conversions; M31 decodes | length≥8; noncanonical bytes return `ok none` |
| `QM31.from_le_bytes` | ranges 0..8 and 8..16; CM31 calls | length≥16; canonical four limbs on success |
| Option `from_residual` | discriminant assertion | Option Infallible can only be none; assertion is not arithmetic |
| `ValidatedRecord.payload` | range-from 5 | framed.length≥5 |
| `decode_k_value` | Usize value*32; byte_offset+product; start+k for each k=1..15; bytes[start+k] for k=0..15; offset_values+value | value<N; byte_offset=32*offset_values; checked outer end `32*offset_values+32*N≤W`; payload length≥that end. Then 32*value, start+15, offset_values+value fit and reads are in range. For direct calls these are premises. |
| `decode_k_loop.body` | iterator next; decode_k_value; out[value] update | iterator 0..N and value<N; outer end guard above; at successor step value+1≤N≤W |
| `decode_k_loop` | Aeneas loop | finite range, same bounds |
| `decode_k` | explicit total checked_mul offset_values*32; checked_mul N*32; checked_add of sizes; payload; checked slice.get; loop | checked_* overflow returns ordinary Length error, not Aeneas failure. framed.length≥5 still required for payload; every inner access is protected by the successful end/length guard. N=0 has no inner calls. |

### Round and prepare orchestration

`ExtractedSemanticRoundsModel.RoundModel.step`: total Usize→U8 cast of
round, U8 `15+round`, alpha[round] update, and boundary child calls.
For round<10, row≤24<256 and update is in bounds. The ten-round caller
uses exactly round=0..9. Transcript sampler `160+row`≤184 and
`next_row+1`≤25 at those rows. No totality conclusion follows for arbitrary
`Boundaries`; decoder, sampler, boundary and value must each be discharged.

`ExtractedPreparedModel.PreparedModel.prepare`: Usize 32+224=256;
U8 31+1=32 or 30+1=31; folded-root unwrap only on two-fold paths;
Vec extension for a 32-byte root and 224-byte round. Scalar/scalar_k use
transcript block at rows 27..32, so absorb's U8 `160+row`≤192.
`folds` is 1 or 2 by the Variant constructors. Child serialization,
ordinary/gamma sampling, queries and claim boundaries are explicit premises.
The historical prepared model's `claim` signature predates reused gamma
powers (S1); it cannot close the optimized `prepared_claim` body.

The shared sampler emission uses Usize j-1 for 0<j≤8, U64 remainder<<32
with remainder<P (result<2^63), Usize 4*i+k (i<8,k≤3), array indexes<8/32,
and i+1≤8 (byte decode) / i+1≤4 (digit extraction). U64 division and
remainder use the nonzero widened P. Since remainder<P, the next dividend is
at most (P-1)*2^32+(2^32-1)<2^63; its quotient by P fits U32 and
remainder<P. Every emitted shift count is 32<64. Digit construction uses its
fixed pass-count bound; none of these
bounds may be obtained by assuming final checked success.

## 4. Cones with no extraction (source-level inventory)

These are **source inventories**, not extracted-function theorems. The
current source files under `crates/aspis-r1-cost-probe/src/` are authoritative;
S1/S3/S4/S5/S7/S9 still owe emitted-body re-pins.

| Function/group | Integer operations and sufficient source ranges |
|---|---|
| `fast_pairing::canonical::reduce` | two U64 folds (+, >>31), guarded U64 subtraction P, U32 casts; all U64 safe as above |
| scalar `add`, `pair`, `reduce_pair` | explicit U32 wrapping_add then guarded sub; total U64 widen/OR/<<32; reduce_pair two wrapping adds and >>31. Canonical packed inputs and sums must be bounded; shifts 32/31<64. |
| `Q::from_limbs/from_m31/limbs/from_wide` | fixed indexes/destructure and comparisons only; private WideExact canonicality is a caller invariant, not a theorem from visibility |
| `Q::add/sub` | packed wrapping adds/subs, four fixed limb reads, shifts32, casts. Packed lanes are <P; each lane sum or offset difference is <2P. |
| `Q::half/half_pow` | U32 >>1, low bit <<30; guarded n≤30, n≠0 then U32 1<<n, subtract1, U8 31-n, shifts n and31-n. n=0 early return; shift counts≤30, subtractions safe |
| `Q::mul_m31` | four U64 widened products, canonical reducer, guard rhs<P; four limbs canonical |
| `Q::raw/mul` | 16 widened products; constant P*P, 2*PP, 3*P; 2*u,2*v; u=fold(cg+PP-dh), v=fold(ch+dg); four ordered raw expressions. Products≤C, partials≤3P. Every ordered addition/subtraction, including pre-subtraction sums, needs bounds. |
| `Q::dot<N>` | assert N≤4; iterator i<N and j<4, array reads/writes; four folded raw accumulations per lane; sum<4B. `neg/square` delegate sub/mul. |
| `Dot::new/push/finish` | literal four lanes; raw and fold; U64 accumulation of <B per push; ≤4096 pushes implies sum<2^46; finish reducer unrestricted |
| `EbyKDot/EbyEDot::new/push/finish`, checked_q, limbs_of, qm31_of | count+1 guarded count<4096; canonical Q conversions; literal indexes; dot as above; finish unwrap requires reducer canonicality. EbyEDot final tower operations use canonical M31/CM31/QM31 leaves. |
| `fast_dots::four_dots` | q[..608]; slot<4, start=0,4,..24; start+4≤28; term<26; scalar offsets 120*slot+4*term+k≤463; g[term] with term<26<29; eight lane indexes<8; U64 products≤C, at most four sum≤4C<2^64; fold<B; seven folded sums<7B<2^37; tail slot*120+104..+120≤480; offset=480+slot*32+term*16≤592 and end≤608, term<2; g[term+26]≤g[27]. Decodes may reject but unwrapping needs canonical-byte premise. |
| `weights::powers/kpowers/double` | fixed-length array construction/field kernels; no local scalar operation except library iterator |
| `weights::field` | Usize i*32,(i+1)*32, slice and unwrap; need (i+1)*32≤bytes.len()≤W and canonical bytes |
| `s2_grouped_inactive_pair` | j<64, group table values<12; group<12, bit<16; U16 1<<bit; 2048-byte canonical f |
| `grouped_inactive_pair` | n=f.len()/32≤64, j<n, s<16, 16*j+s<1024; group scan group≤groups≤64; group insertion requires group<64 (at most one per j); groups/group increments≤64; bit<16 |
| `twofold_libra_weights` | side<2, j<4, s<16; index=16*j+s≤63; guard index<56 implies index/28<2, index%28<28 |
| `factored_s2_libra_weights` | side<2, r<4, PERM[r]<4; fixed index reads/writes; no variable integer arithmetic beyond loop increments |
| `Weights::new` | k<3,d<5, TAU permutation of0..4: 2*TAU[d]≤8, 9-2*TAU≥1, 8-2*TAU≥0; k<2 for circle factors: 3+k<5; d=1..4; all dimensions 5×5×4 /3×10 |
| `Weights::raw` | kind∈0..6,j<1024; row(j)<1024; kind4 guard j<56 then j/28<2,j%28<28; kind1..3: kind-1<3, b<10, 9-b≥0, 1<<b count<10; other branch kind5/6 gives kind-2=3/4, d<5,2*d≤8, (j>>(2*d))&3<4 |
| `scalar_factor` | s<4, PERM[s]<4; field ops only |
| `tensor` | folds∈{1,2}, d<5,k<5; n=4^(d-folds), n≤256; j<n,s<4: j+s*n<4*n≤output.len(); n*=4≤1024 |
| `dual_raw` | alpha.len()∈{1,2}; 2*len≤4, width=1<<(2*len)∈{4,16}; s<width, s%4<4,s/4<4; width*j+s<1024 |
| `Weights::pair` | folds∈{1,2}; shift 2*folds≤4, n=256/64; scratch n, parts7, all kind indexes≤6; k=kind-1 orkind-2<5. Shared path: j<16,s<4,16*s+j<64; fixed PERM, masks<16; 4*j+s<1024; j+7*side<14 for j<7,side<2; all final seven indexes<7. Requires f exact n*32 canonical bytes, alpha of length folds. |
| `dense_point_pair` | kind∈1..3, alpha.len=2; b<10,9-b≥0; width≤512 at update, j+width<1024, width*=2≤1024; j<64,s<16 implies16*j+s<1024 and Variant::row<1024 |
| `materialize` | 1024 allocated entries; j<1024,kind<7; no integer products outside field calls |
| current `prepared_claim` | seven/twenty-nine fixed arrays and reused gamma powers; all loops index their fixed extent; historical extraction is stale (S1) |

Source `cfg(prover)` trace-index multiplications are not deployed verifier
operations. Parser and Merkle traversal arithmetic is explicitly outside this
job. Geometry/basis callers need their own range links; arbitrary public calls
to raw/field/pair are not admitted just because Rust makes them public.

## 5. Input premises and where they come from

Canonical parsed M31 limbs `<P` are **input premises** at arithmetic leaves.
The strict field parser theorem supplying the codec connection is
`AspisR1.ActualDecodeKStrictQM31Parser.source_refines`
(`lean/ActualDecodeKStrictQM31Parser.lean:26`), with
`success_has_strict_limbs` at line 40. This does not prove the whole outer
indexed decoder is total. Its existing success-canonicality proof establishes
caller output canonicality only after a successful decoded result.

For `fast_dots`, current `View::parse` checks the 26 M31 values, one QM31 tail
and two additional QM31 values per slot before arithmetic use. For weights,
it checks canonical WideExact y1/round/final-message payloads. These are
source observations; the new parser must re-establish them after the format
change. `WideExact`/private Q constructor visibility is not a formal range
premise discharge. Alpha/gamma/kappa/rho require sampler output canonicality;
intermediate field operations must preserve it. Semantic arrays require
canonical polynomial coefficients and selected alpha, plus round<10.

Batched rho additionally requires a distinct-index row traversal and shared
terms cadence: raw lanes at phase t must be `<B+(t%4)*C`; canonical inputs
alone do not bound a mutable U64 accumulator. Raw/vector length bounds and
fixed alpha slice lengths are separate premises, never silently inferred
from eventual successful checked execution.

## 6. Theorems (proved, reused, open)

Existing theorem sources (fresh focused replay status is recorded in the manifest and theorem index):

| Theorem | Source location | What it establishes |
|---|---|---|
| `RawExtractedSemanticCallOpsV23.generated_qm_add_exact` / `generated_qm_mul_exact` | `lean/RawExtractedSemanticCallOpsV23.lean:25`, `:44` | emitted field calls total and canonical on canonical inputs |
| `RawExtractedSemanticPolynomialWrappersV1.semantic_boundary_refines_polynomial_endpoints` | `lean/RawExtractedSemanticPolynomialWrappersV1.lean:26` | total emitted boundary, canonical result, polynomial meaning |
| `RawExtractedSemanticValueLoopV1.semantic_value_refines_polynomial_eval` | `lean/RawExtractedSemanticValueLoopV1.lean:178` | total emitted Horner wrapper under canonical/round premises |
| `AspisR1BatchedWeightsPushBodyBoundedV6.push_body_step_bounded_of_state` | `lean/AspisR1BatchedWeightsPushBodyBoundedV6.lean:16` | total selected emitted push iteration under index/cadence ranges |
| `AspisR1BatchedWeightsPushLoopAllPrefixV11.push_loop_all_prefix` | `lean/BatchedWeightsPushLoopAllPrefixV11.lean:49` | whole emitted push loop, range propagation |
| `BatchedWeightsPushOuterFlushV13.push_flush_success` | `lean/BatchedWeightsPushOuterFlushV13.lean:21` | emitted outer flush after safe push loop |
| `AspisR1BatchedAllPrefix.run_invariant` / `value_after_any_prefix` | `lean/AspisR1BatchedAllPrefix.lean:64`, `:205` | source-shaped prefix range/residue; actual retained reducer; not whole caller |
| `FastDotFoldedBatches.actual_reducer_after_seven` | `lean/FastDotFoldedBatches.lean:73` | mathematical batch/reducer composition, not actual fast_dots loop |
| `PreparedReachability.prepare_success` | `lean/ExtractedPreparedReachability.lean:82` | success inversion only; insufficient direction for R22 |

Exact line anchors are regenerated in `evidence/overflow-freedom-20261019/theorem-index.json`.
Earlier R22 field/tower packets under `lean-candidates/r22-current-field-wrapping-20261019/`
prove checked/wrapping equality for primitive kernels and canonical output;
their reports explicitly exclude optimized private fast-pairing bodies.

Fresh replay on 2026-10-20: all six prior R22 scalar/field/tower modules,
the raw-pairing range draft, semantic add/mul/boundary/value targets, both
rho outer-push branches, the all-prefix invariant and fast-dot reducer
composition now compile locally. Exact hashes, exit status, wall time, peak
RSS, swaps and full axiom reports are retained under the packet's receipts.
No existing Lean source was edited. Missing cache dependencies were compiled
into `/tmp/r1-overflow-free-20261019-objects`; no shared object was overwritten.

New totality modules and their final statuses are listed in the packet report.
They distinguish successful Aeneas execution returning a Rust error from an
Aeneas overflow/index failure. Their framing, range and canonicality premises
are explicit; none assumes the checked execution it is intended to prove.

## 7. Findings

No admitted-input overflow counterexample has been established by this
review. This is not a proof that all operations are safe. Arbitrary direct
helper inputs can overflow (e.g. noncanonical M31 add, unbounded decoder
value*32 or mutable raw accumulation); the required caller range hypotheses
must not be omitted. No Rust wrapping/checked choice was changed.

The historical 10 GiB gate is superseded by the revised local rules:
shared mkdir lock, no concurrent `lean -M4400`, own object directory. It is
no longer a blocker. Import-loading failures and their replacement dependency
builds are retained in the manifest. No memory cap was raised.

## 8. What remains

R22 remains OPEN. Needed before declaring the requested stage-1 proof complete:

1. The raw arithmetic draft and listed existing totality targets have fresh
   focused receipts. This is not a coherent release-manifest replay of the
   complete deployed verifier closure.
2. The new actual value/loop decoder totality theorems discharge inner
   arithmetic/iterator obligations under explicit payload/end bounds. Connect
   the outer size/slice guards, framing and parsed/sampled canonicality to
   callers; distinguish ordinary rejection from Aeneas failure.
3. Connect all ten semantic rounds and prepare children with total-execution
   statements, not success-inversion lemmas.
4. Re-emit/re-pin optimized weights, private fast_pairing and fast_dots, then
   prove bounds against those actual definitions (including packed operations,
   casts, library iterators and array/slice accesses).
5. Compose batched rho global phase/cadence invariants with the actual stage-1
   caller and canonical power/basis selection.
6. Derive the deployed-acceptance ⇒ model-acceptance bridge. Stage 2 remains
   after its extraction; the replacement parser and Merkle paths are excluded.

No full manifest replay, Rust/SBF rebuild or release acceptance claim is made.

## 9. Resume proof packet (2026-10-20)

The previously blocked raw-coordinate draft now compiles. New modules
`R22DecodeValueTotal`, `R22DecodeLoopTotal`, `R22BatchedPushTotal`,
`R22BatchedValueTotal`, and `R22ControlBounds` compile in dependency order,
with no changes to existing Lean source. They provide actual decoder
value/loop totality, both-phase actual rho push totality, unrestricted-row
actual rho value totality with canonical output, and symbolic control/index
bounds. All their premises and exact theorem locations are in
`../evidence/overflow-freedom-20261019/theorem-index.json`.

The combined `R22OverflowAudit` checks 50 public theorem axiom reports.
The manifest records 36 successful focused targets; every accepted axiom
report uses only standard axioms. This is focused proof evidence, not a full
release closure or a completion of the optimized-body/caller obligations in
section 8. Full metrics, failed attempts and the precise remaining frontier
are in the packet's `REPORT.md`.
