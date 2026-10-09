# V7 end-to-end exact-semantics closure audit

Status: incomplete. This is a source/statement audit, not a Lean verification
result or an end-to-end release certificate.

Audited source revision: `05a93636833a7a832ca382ff62d05f1d4f4b8ff7`.
The worktree was clean at the start of this audit. The existing 336-target
replay is recorded in [the frozen replay evidence](v7-r30-frozen-replay-evidence-20261001.md).
That replay verifies the statements in its manifest; it does not strengthen
canonicality statements into exact arithmetic identities.

## Completion criterion

Literal production observer acceptance must yield both the maintained
terminal relation and an exact interpretation of the decoded and folded
query values appearing in that relation. Every canonicality, cache,
challenge-power, coordinate, and arithmetic-bound premise needed for that
interpretation must come from the retained successful source execution.
No post-decode callback may be replaced by a gamma-validation prefix or an
uninterpreted canonical value. V8 research is not evidence for this V7 goal.

The existing extraction, callback-staging, hash-oracle, and mathematical
security boundaries must remain explicit. This criterion does not silently
claim a separate cryptographic soundness or Fiat--Shamir probability theorem.

## Requirement-by-requirement audit

Paths below are relative to
`aeneas-verif/v7-k13-current-caller-release-source-20260914` unless noted.
“Missing” means the cited checked statement does not supply the required
guarantee; it does not claim that every historical file has been exhaustively
searched for a possible reusable lemma.

| Boundary | Current evidence | Required additional evidence |
| --- | --- | --- |
| Packed bytes to M31 words | `proof-r30/V7ProductionCallbacksR30PackedDecoderCanonical.lean`: `successful_packed_decoder_canonical` proves canonical output words. | A generic exact byte/word correspondence, including length and eight-word block order, for every successful decoder call. |
| Checked field primitives | `proof-r30/V7ProductionCallbacksR30FieldCanonical.lean` has checked/wrapping M31 source equalities and canonicality theorems. `proof-r26/V7CallerCurrentReleaseR26FieldBridge.lean` has exact M31 operation results. | Exact callback M31, CM31, QM31, half, and scalar-multiply results, preserving the field image as well as canonicality. |
| Prepared caches | `proof-r30/V7ProductionCallbacksR30Qm31Canonical.lean` proves canonical prepared multiplication results. | Source `new` must establish the nine-cell operational/semantic cache relation; source `mul` must return the represented product. Derive cache relations for actual gamma and alpha powers. |
| Delayed three-product arithmetic | `proof-r30/V7ProductionCallbacksR30KaratsubaCanonical.lean`: `successful_prepared_sum_products3_canonical` explicitly excludes dot-product and overflow claims. | Exact source channel accumulation, justified checked-operation bounds, exact reconstruction, and the unfused three-product identity. |
| C1 gamma combination | `proof-r30/V7ProductionCallbacksR30GammaC1Canonical.lean` proves canonical output through the literal slot-major callback. | Exact componentwise weighted sum of the 26 decoded columns per slot, with four-product chunk reductions and the two-column remainder preserved. |
| C2 and packed gamma | `proof-r30/V7ProductionCallbacksR30PackedGammaCanonical.lean` retains successful decoder calls and canonical words. | Exact helper-major limb packing and the three prepared helper products added to the C1 result; compose with exact byte decoding and actual power provenance. |
| Normalized arity-four fold | `proof-r30/V7ProductionCallbacksR30NormalizedFoldCanonical.lean` explicitly excludes the polynomial identity. | Exact cubic coefficients and evaluation, actual alpha/alpha-square/alpha-cube cache provenance, and canonical/semantic provenance of all coordinate inverses. |
| Sixteen query callbacks and terminal relation | `proof-r30/V7ProductionCallbacksR30QueryValuesCanonical.lean` proves canonical query values. `proof-r30/V7ProductionSnapshotObserverR30ProductionClosure.lean` derives the maintained terminal identity from production acceptance. | Index-preserving exact query correspondence through the actual openings and `from_fn` loops, then an acceptance theorem that exposes this correspondence alongside the terminal relation. |
| Release verification | Existing focused audits and one green frozen canonical/terminal replay. | Focused new exact-semantic targets, dependent bridges, consolidated permitted-axiom audit, and a newly frozen manifest/replay covering the stronger endpoint. |

The terminal identity currently uses `dispatch.foldedValues` inside
`threeRoundValueVector`. Its production derivation discharges representation
and layout premises, but does not identify those values with the mathematical
gamma/normalized-fold formulas. This is the load-bearing missing connection,
not a reason to discard the existing terminal proof.

## Source facts controlling the proof route

### Exact packed decoder

The staged source comes from
`../v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque`.
`FunsChunk07.lean` defines the outer decoder; `FunsChunk06.lean` defines the
eight-byte little-endian load closure and the invalid-flag scanner.

For each 31-byte block, the first seven output words use eight-byte loads at
byte offsets `0, 3, 7, 11, 15, 19, 23`, shifted right by
`0, 7, 6, 5, 4, 3, 2` bits respectively, then masked by `P = 2^31 - 1`.
The eighth word uses the final four bytes at offset 27, shifted right by one
bit and masked by P. The output base is `8 * block`.

The intended pure specification is extraction of consecutive 31-bit words
from little-endian bytes, not reduction modulo P. The all-ones 31-bit word
equals P and must be rejected, not mapped to zero. Prove a bounded block
lemma symbolically, then an outer processed-prefix invariant. Do not unfold
all 104 or 48 words or evaluate a huge whole-input numeral.

### Exact prepared three-product helper

`FunsChunk06.lean` defines callback
`qm31_sum_products3_prepared` with a zero-initialized 3-by-3 U64 channel
matrix, three input products, and final Karatsuba reconstruction. Inner
channel multiplication and accumulation use checked scalar operations.

The R26 reusable route is in
`proof-r26/V7CallerCurrentReleaseR26PreparedSum3Semantics.lean`:

- `PreparedFor` identifies all nine canonical cached channels with the
  represented QM31 value.
- `PreparedArrayFor3` and `GeneratedCanonicalQM31Array3` state the required
  input representations.
- `OuterChannelInvariant` tracks each channel's natural bound and exact
  field image after the processed input prefix.
- `generated_outer_loop_corresponds` proves the R26 loop invariant.
- `generated_reconstruction_corresponds` gives canonical and exact
  Karatsuba reconstruction for any U64 channel matrix.
- `exactProductDot3` is the intended three-product result.

R26's public theorem `generated_add_sum_products3_prepared_corresponds`
includes a fused constant. The R29 callback above does not. It is not valid
to identify those public functions definitionally. Reuse or adapt the
bounded loop and reconstruction facts, and prove the actual unfused source
identity. The private R26 algebraic reconstruction lemma may require a
public wrapper or a small explicitly reviewed refactor.

With canonical input channels, each product is at most `(P-1)^2`. Three
products fit U64, and the R26 symbolic four-product bound is already
available. These bounds must justify each checked operation, not be added
as unsupported release-level assumptions.

### Exact gamma combination

The literal C1 graph is in
`../v7-tag73-current-caller-source-20260830/proof/V7GammaSlotMajorLiteral/Funs.lean`.
For each slot it reads `c1[26 * slot + column]` and
`powers.base.c1_limbs[column][limb]`. The 26 columns are processed as six
four-column chunks plus the final two columns. Each chunk is reduced per
limb before being added to the wide totals; the totals are reduced again at
the end. A componentwise field-sum invariant respects this actual route.
Bounds on both canonical decoded inputs and canonical power limbs must be
derived before using checked accumulation.

For C2, `FunsChunk07.lean` reconstructs helper `h`, slot `s` from four
consecutive words starting at `4 * (4 * h + s)`. The helper powers are
`powers.base.helpers[0]`, `powers.base.helpers[1]`, and `powers.d` in that
order. The three-product helper result is added to the C1 slot value.
The exact theorem must preserve this order and prove, not assume, the
correspondence of the power object to its source gamma construction.

### Exact normalized fold

`FunsChunk06.lean` defines the candidate with the following field formulas:

```
L = q0 + q1                     R = q2 + q3
D = (q0 - q1) * inv0            E = (q2 - q3) * inv1
constant  = (L + R) / 2 / 2
linear    = (D + E) / 2
quadratic = (L - R) / 2 * inv2
cubic     = (D - E) * inv2
result    = constant + alpha * linear
                     + alpha^2 * quadratic + alpha^3 * cubic
```

The circle wrapper passes inverse entries in order
`[inv_2y, -inv_2y, inv_2x]`. The caller constructs the three prepared alpha
powers by source square, multiply, and `new` calls. The exact query-fold
theorem must retain and interpret those source equations.

The pure algebraic lemma
`AspisV5ComponentCConcreteFoldLinearity.lineFoldValue_eq_polynomial` in
`AspisFormal/AspisFormal/V5ComponentCConcreteFoldLinearity.lean` already
relates this polynomial to the nested fold. That file explicitly does not
prove byte decoding or source correspondence. Reusing its scalar identity
does not import a V5 or V8 release claim into V7.

Current coordinate canonicality evidence is specifically about `line_x`;
it is not an exact inverse/coordinate certificate. Derive the inverse
premises from successful coordinate preparation and its source point/batch
inversion equations before composing the fold semantics.

## Next focused increment and verification sequence

The smallest useful new exact leaf is a successful-output M31 reduction
theorem. The proof route already exists in
`successful_callback_reduce_canonical`: rewrite using
`callback_reduce_u64_eq_current_reduce_u64_wide`, obtain
`generated_m31_reduce_u64_corresponds`, and retain its final exact equality
instead of discarding it. The intended conclusion contains both canonicality
and `generatedM31ToExact output = (value.val : ExactM31)`. No new arithmetic
premise is needed beyond the U64 type bound.

Then retain exactness for the checked callback field operations and prepared
cache construction, prove the source three-product identity, and compose the
exact gamma/fold callbacks. The packed byte correspondence is an independent
generic branch and must join the same final acceptance theorem. Audit and
derive actual challenge/cache/coordinate provenance before closing the
sixteen-query bridge.

For each increment: compile the smallest changed `.lean` first, then its
dependent bridge, then print axioms. Use the pinned remote workspace/cache
and `toolchain/check-r30-decoder-focused.sh`, inside a dedicated
`systemd-run --user --scope` with `MemoryHigh=7G`, `MemoryMax=8G`, and
`MemorySwapMax=0`. Record target, exit, wall time, peak RSS, swap, revision,
and axioms. Commit and push only verified green increments. Freeze the
stronger dependency graph and run its full manifest only after its endpoint
is ready; do not rerun the unchanged canonicality manifest.

## Current execution blocker

On 2026-10-02, the read-only connectivity check

```
ssh -o BatchMode=yes -o ConnectTimeout=5 dombarker@100.108.41.90 'printf remote-ready'
```

returned exit 255 with
`ssh: connect to host 100.108.41.90 port 22: Operation not permitted`.
This session's permissions also designate `/Users/dominic/ZK/.git` read-only.
No compatible local Aeneas/V7 compiled cache was found in the preceding
local cache inspection. No cold local dependency build, new Lean replay,
Git metadata mutation, commit, or push was attempted in this audit.

Restore build-host network access and Git write access to resume verified
proof increments. This document introduces no unverified proof declarations
and makes no claim that the active end-to-end goal is complete.
