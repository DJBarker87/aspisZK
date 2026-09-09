# Actual two-entry OOD interpolant and repaired affine claim

Research continuation from `33e13de4e4b8bfdef7f3f2fb2e472b34db44865e`.
The research worktree was clean when inspected. Only new formal research
files, this report and focused evidence are owned by this continuation;
concurrent Rust/payment/source work and main are preserved.

Status: the sparse interpolant core, dependent actual row constructor and
exact-QM31 inverse adapter are kernel-checked. The previously free affine
interpolant is now constructed, and the actual two-entry scalar subtraction
is proved equal to the row game's correction. This is not an actual-verifier
acceptance theorem.

## What the construction actually fixes

The preceding [interleaved chord bridge](interleaved-chord-review.md) used an
explicit total reconstruction map but left the affine interpolant vector as
a constructor input. Here that vector is constructed from the actual OOD
formula, including the equal-x branch:

```
useX = (x0 != x1)
h0 = useX ? x0 : y0; h1 = useX ? x1 : y1
Y0 = sum(lane=0..28, gamma^lane * answer0[lane])
Y1 = sum(lane=0..28, gamma^lane * answer1[lane])
slope = (Y0-Y1) * inverse(h0-h1)
intercept = Y0 - slope*h0
I = single(0,intercept) + single(useX ? 2 : 1,slope)
```

The literal chord signs are
`a=x0*y1-y0*x1`, `b=y0-y1`, `c=x1-x0`.
The two supplied answers may be false, zero or equal: the theorem states
that their constructed interpolant evaluates to them, not that they equal
an honest component polynomial. No circle hypothesis is necessary for this
interpolant identity. The chord/reconstruction evaluation elsewhere still
requires the actual circle equation and image conditions.

[OODInterpolantCore](experiments/OODInterpolantCore.lean) derives the sparse
even/odd coefficient halves and evaluates them through the maintained
`initialP0/initialP1` natural-basis polynomial convention. Coefficient 1 is
the y basis element; coefficient 2 is x, not the reverse. A sparse line sum
is proved symbolically with one surviving index; no 1024-entry basis is
enumerated or reduced.

[OODInterpolantRows](experiments/OODInterpolantRows.lean) packages the two
29-element OOD vectors, both points and gamma, computes those batches and
installs the resulting I and chord in the concrete `Rows` constructor. Its
`vector_fibre` retains the actual stored-fibre slot order
`(x,y),(x,-y),(-x,-y),(-x,y)`:

| Selected coordinate | Interpolant values in source slot order |
|---|---|
| x | `[u+v*x, u+v*x, u-v*x, u-v*x]` |
| y | `[u+v*y, u-v*y, u-v*y, u+v*y]` |

This is not a substitution of an old raw-word matching definition for V8's
virtual quotient; it is the actual interpolant inside that quotient's
numerator.

## The two-entry subtraction is the whole affine correction

The ordinary weight is constructed as
`w0 + kappa*w1 + kappa^2*w2 + kappa^3*w3`, retaining the inactive row as the
constant term and all three point rows with strictly positive powers.
The generic dot identity derives this functional from the four covectors.
Then the sparse interpolant theorem gives exactly

```
ordinaryFunctional(kappa, I)
  = intercept*ordinaryWeight[0]
    + slope*ordinaryWeight[useX ? 2 : 1].
```

`Data.corrected_claim` equates the actual two source subtractions with
`Rows.correctedClaim`. `Data.source_prior` consumes the existing shifted
row theorem to identify the resulting discrepancy polynomial using the
same concrete chord map and constructed interpolant. No assumed
`inactiveExact`, interpolant equality, transpose-dot equality, codeword
membership or payment witness appears in those hypotheses.

The four original covectors and four scalar claims remain explicit inputs.
The zero-index and selected-index public weights correspond to
`Description.entry`/`entry_pair`; equality of those optimized computations
with the semantic selector/mask expression is not proved merely by naming
the weights here. Likewise, the mathematical sum over 29 lanes is not a
Rust loop/Horner or shared-gamma translation theorem.

## Source and causal boundary

Inspected at the stated pin:

| Source | Relevant operation |
|---|---|
| `inactive_row_binding.rs:56` | First OOD point, absorption of `[359..388]`, bounded distinct second point, absorption of `[388..417]`, then gamma |
| `structured_weights.rs:122` | Absorb inactive claim `[358]`, sample kappa, construct the repaired three scales and gamma batches |
| `structured_weights.rs:144` | Actual x/y selection, inverse, two coefficients and chord signs |
| `structured_weights.rs:160` | Read public entries 0 and 2/1; subtract the two affine contributions |
| `structured_weights.rs:163` | Compact functional description and corrected scalar bound before tau |
| `relation_callback.rs:126` | Source four-slot coordinate order and interpolant subtraction in each query numerator |
| `crates/aspis-core/src/field.rs:918` | QM31 non-panicking inverse formula and zero rejection |

Both OOD vectors and both points are fixed before gamma. The first vector
is absorbed before the second point is sampled; the second vector may
depend on that later point. Gamma precedes the inactive claim/kappa boundary.
Although source code computes the interpolant after sampling kappa, none
of its determining inputs uses kappa. `Data.checked_inverse_eq` proves the
inverse is uniquely determined by the selected point denominator. This
does not by itself prove an actual transcript's causal-prefix law.

The field predicate `Checked` is `(h0-h1)*inverse=1`. It is an algebraic
specification of a successful inverse, **not a newly added runtime product
check or an unchecked prover inverse hint**. The source computes the inverse
itself and rejects zero. The generic theorem derives nondegeneracy of the
actual chord from that specification, including equal x with unequal y.

[OODInverseBoundary](experiments/OODInverseBoundary.lean) directly reuses the
proved literal QM31 tower formula `qm31TryInv_eq`, also consumed by V7's
`successful_qm31TryInv_is_inverse`, to provide Checked from exact-tower
`qm31TryInv = some inverse`. This is not a fresh proof of tower inversion.
The existing Rust/primitive formula seam remains distinct from this
mathematical source-form adapter. No q16 schedule, grinding law or V7 security
budget is imported.

The first adapter preflight deliberately refused to consume the broader V7
secure-circle module: its indirect `V7Tag73DeterministicRefinement` source
differed between pinned research and the concurrent main cache. It stopped
before Lean. The retained adapter imports only the needed exact-tower module;
that entire narrower source/olean closure passes the pinned check. No cache
was overwritten, broad replay started, or main work altered.

## Remaining obligations and cost scope

No actual Rust translation is claimed. Canonical parsing and wire offsets,
the compiled public selectors/grouped masks, optimized shared-gamma and
structured carry loops, real transcript chronology and sampler/FS law still
need their respective source connections. This work neither assumes a
received oracle is globally polynomial nor proves adaptive recovery or a
checked payment witness. Those accepted failure events remain in the ledger.

This formal-only subtask adds no protocol changes, new messages, extra scalar
fields or verifier operations; concurrent research changes are reported
separately by their owner. Its body model stays 40,282 bytes. Existing full-transaction CU and
full-view ZK/Fiat–Shamir obligations are unchanged; Lean timings below are
not prover/extractor/CU measurements. No grinding credit is used.

## Focused evidence

Commands from the research repository root, with fresh log paths:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_ood_interpolant.sh OODInterpolantCore /absolute/NEW-core.log
bash docs/research/v8-no-work-100-20260907/experiments/run_ood_interpolant.sh OODInterpolantRows /absolute/NEW-rows.log
bash docs/research/v8-no-work-100-20260907/experiments/run_ood_interpolant.sh OODInverseBoundary /absolute/NEW-inverse.log
```

The runner pins source imports to the checkpoint, checks cached source/olean
hashes before/after, resolves the cached Lake environment, and runs only the
named leaf with `-M7000`, an independent 7-GiB aggregate-RSS guard and no
concurrent builds. All unchanged predecessor leaves are reused, not replayed.

Core v5: exit 0; 8.86 seconds wall; 5,645,844,480 bytes peak RSS; zero swaps;
three audits contain only standard axioms. Core source SHA-256:
`46e1d6d59ef3ca582278c0edbc96a187d6cc73efa738fa921625093af86727c0`;
olean: `07c881319fb74c5e94ecc438cf1134f02d6124101081482bb59ceba98418c58c`.
Earlier bounded core diagnostics exposed sparse-sum simplification, an
unresolved half-width in `Fin(2*n)` inference, and a Bool branch reduction.
These were corrected symbolically without raising limits; no guard kill.
The v2 command initially had a mistyped path and exited 127 before executing
Lean; the corrected recorded v2 run is the actual focused diagnostic.

| Retained target / successful log | Exit | Wall seconds | Peak RSS bytes | Swaps | Axiom audits |
|---|---:|---:|---:|---:|---:|
| [Core v5](experiments/ood-interpolant-core-v5.log) | 0 | 8.86 | 5,645,844,480 | 0 | 3 |
| [Rows v3](experiments/ood-interpolant-rows-v3.log) | 0 | 8.54 | 5,616,631,808 | 0 | 8 |
| [Inverse v3](experiments/ood-inverse-boundary-v3.log) | 0 | 10.14 | 5,634,818,048 | 0 | 1 |

All audits use only the standard `propext`, `Classical.choice`, `Quot.sound`
subset. There are no retained `sorry` or new axiom declarations. All runs
observed research HEAD at the checkpoint above and read-only main/cache HEAD
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. The runner checks and records
source and olean hashes before and after, with `PROVENANCE_UNCHANGED=true`.

Rows source SHA-256:
`d39031018a1f93f2f227406ad2fdc18c79638f511d1f06cbbf8a7e496871a24a`;
olean: `4e5556c139409847803dd84c1a481e6f7ae65aedb8ca69e3fc2c1712190532ee`.
Inverse adapter source:
`a576ff507a8f11a9504ecd3544477a247a845e988afd83018cd5250c9bafcebb`;
olean: `b4b01d082ceeade04b38235dc602ea3fffd25b96f3465ce80ae5658939d869c8`.

All earlier logs are retained as failed diagnostics, not proof evidence:

| Preflight | Exit | Wall seconds | Peak RSS bytes | Resolution |
|---|---:|---:|---:|---|
| Core v1 | 1 | 27.17 | 5,501,337,600 | Sparse single-sum lemma and explicit types |
| Core v2 | 1 | 6.97 | 5,498,699,776 | Explicit sparse-vector type and outer polynomial definition |
| Core v3 | 1 | 9.27 | 5,469,339,648 | Explicit half-width `n=512` in coefficient-map statement |
| Core v4 | 1 | 8.13 | 5,503,369,216 | Literal Bool false-branch simplification |
| Rows v1 | 1 | 8.49 | 5,504,466,944 | Correct decide lemma and typed covector application |
| Rows v2 | 1 | 15.65 | 5,507,481,600 | Named chord coefficient and tiny `Fin.succ` reductions |
| Inverse v1 / diagnostic v2 | 2 | Not timed | Not measured | Provenance stopped before Lean; narrowed import |

Every measured failed Lean run used zero swap; none reached the guard. No
limit was raised. The source-returned inverse adapter and all successful
endpoints are separate from those failed log outputs.

Next concrete source connection: prove the compiled original selector/mask
weight entries and structured carry evaluation implement the now-explicit
ordinary functional, retaining the compact pre-tau description binding.
Recovery coverage, a checked witness and resource-bounded FS do not follow
from closing this deterministic OOD interface.
