# Covered quotient support to original symbols and OOD GRS values

Research parent: `9254b2416c3f8c3c488d0475a00d812fee836e00`.
Status: both new leaves are kernel-checked on the NUC. Each has seven
standard-only axiom audits; no `sorry` or new axiom occurs in retained proofs.

## Reuse and the sharper support boundary

The core chord/image identity was already proved in
`SelectedQuotientOriginal.encoded_original` and
`symbol_agreement_iff`. It uses the literal natural1024 reconstruction,
two-entry OOD interpolant, actual stored log20 encoder, and exact child
indices. The existing `fibreBad_card` drops at most two complete fibres,
which is appropriate for its near-radius application but unnecessarily
coarse at the new family threshold.

The new `CoveredOriginalSymbols` adapter keeps symbol-level pole accounting:

```
Q in literalFamily(actual virtual quotient)
  -> at least 9,558 matching complete fibres
  -> at least 38,232 distinct stored matching symbols
  -> at least 38,230 original-code matching symbols.
```

The last step uses `poleSymbols_card <= 2`, not `poleFibres_card <= 2`.
Its exact support inclusion is the quotient symbol support minus the two
possible pole symbols, contained in the reconstructed original symbol
support. This preserves the strict historical V7 threshold `38229 < support`.
Dropping two whole fibres would leave only 38,224 symbols and fail that gate.

The original candidate is constructed as
`U = d.original Q = reconstruction(a,b,c)(Q) + interpolant`.
Its code membership is by the actual natural-message encoder, not a supplied
component tuple. `selected_width29_valid` uses the actual C1/C2 raw batch and
constructs a possibly gamma-adaptive `Width29ProximateStrategy`, then proves
the literal V7 `Width29ValidResponse` predicate. The historical curve formula
uses `value * gamma^lane`; the source batch uses the commutatively equal
`gamma^lane * value`. No coefficient order is permuted.

This proves the validity input to V7 correlated agreement. It neither
replays that large theorem nor improves its challenge cap, nor concludes
matching original components at each gamma. The gamma-dependent quotient
or original candidate is not moved before gamma. No dominant C1 decoder,
candidate tuple membership, global received polynomiality or payment witness
is assumed.

## Source OOD exclusion versus the weaker checked-data interface

The actual research `inactive_row_binding.rs::to_gamma` calls
`Transcript::challenge_secure_circle_point` for both points and checks they
are distinct. `crates/aspis-core/src/transcript.rs` uses
`secure_ood_circle_point_from_parameter`; `circle.rs` rejects a singular
rational-map denominator and then any parameter in CM31. Successful points
are therefore outside the M31 stored circle domain. The pinned V7
`V7Tag73SecureCircleMap` formalization already models this exact check order.

By contrast, `OODInterpolant.Data.Checked` currently states only the
selected-coordinate inverse equation. It does not include circle equations,
the exclusion of the west pole or the sampler's subfield exclusion. The new
support adapter deliberately works under this weaker established interface
and preserves the two-symbol loss. Proving global nonpole from successful
sampler outputs is a legitimate stronger future composition, not an assumed
consequence of `Data.Checked`.

A zero-loss claim from `Data.Checked` alone is false: choose two distinct
stored circle points as the chord endpoints, a zero interpolant and Q=0,
and a raw word nonzero only at one chord endpoint. Totalized division makes
its virtual quotient zero everywhere, while the reconstructed original
zero word mismatches that raw endpoint. Those endpoints are rejected by the
actual OOD sampler, so this is an interface falsifier, not a legal sampled
transcript or an acceptance/security counterexample.

## Pointwise OOD-to-GRS bridge

The separate `CoveredOODGRS` leaf reuses the actual V7 GRS message map:

```
GRS(U) = circleNumerator(initialP0(U), initialP1(U))
t = y/(1+x)
GRS(U)(t) = (1+t^2)^512 * circleFunctional(x,y,U).
```

This identity holds at any circle point with `x != -1`; it is proved by
`circleNumerator_eval_stereo`, not extrapolated from stored-point agreement.
The actual natural message has both circle polynomials of degree below 512.
`ComponentOODBinding.original_point_values` then supplies both literal
batched OOD values, giving

```
GRS(d.original Q)(t_r) = (1+t_r^2)^512 * d.batch(r).
```

The multiplier is a nonzero **multiplication**, not a division. It depends
only on the OOD point; after that point is fixed, a degree-28 gamma answer
polynomial remains degree at most 28 after scaling. The theorem assumes
checked data, the two literal image equations, both circle equations, and
the chosen point's west-pole exclusion. It assumes neither correctness of
individual OOD component answers nor a recovered component tuple.

These interfaces let a subsequent argument test a pre-OOD interpolation
polynomial at the actual OOD answer polynomial. They do not prove that the
resulting gamma polynomial is nonzero. Identity cases, source/sampler
coupling, authenticated recovery, runtime bounds, the literal payment
endpoint, full-view ZK and resource-bounded Fiat–Shamir remain explicit.

## Cost and evidence boundary

No production source, verifier check, transcript message, query count or
proof field changes. The maximum body remains 40,282 bytes, q22/QM31 and
all carried-image/shifted-row/shifted-query repairs remain intact. No CU,
prover-time, complete-transaction or work-security claim is added.

Only the new focused targets and a tiny instance diagnostic ran on the NUC
under the pinned 9254 research / 26a9 borrowed closure. No existing leaf,
large interpolation proof, SBF build or full regression was rerun.

| Target/run | Exit | Wall time | Peak RSS (KiB) | Swaps |
|---|---:|---:|---:|---:|
| CoveredOriginalSymbols v1 | 0 | 3.23 s | 6,856,640 | 0 |
| CoveredOODGRS v1 | 1 | 5.51 s | 6,799,768 | 0 |
| CoveredOODGRS v2 | 1 | 5.53 s | 6,804,508 | 0 |
| CoveredOODGRSTypes diagnostic v1 | 0 | 2.67 s | 6,802,256 | 0 |
| CoveredOODGRS v3 | 1 | 6.51 s | 6,803,828 | 0 |
| CoveredOODGRS v4 | 0 | 10.89 s | 6,838,648 | 0 |

The OOD v1 failure isolated concrete specialization of the existing
stereographic theorem. V2 introduced generic field helpers but exposed a
missing generic `DecidableEq` and a remaining concrete specialization
recursion. The explicit-type diagnostic showed the selected and generic
power operations use the same Field-to-Monoid path, rather than different
mathematical powers. V3 checked all four generic helpers and abstracted the
parameter and denominator before specialization; only terminal field-instance
traversal remained. V4 permits recursion depth 400 solely at those two exact
applications, retaining depth 200 elsewhere. No heap, heartbeat, mathematical
statement or arithmetic algorithm was changed. Exact failed source snapshots,
logs and manifests are retained. Two harmless unused-`DecidableEq` warnings
remain visible in the green log.

Commands, after staging each target in the fresh pinned overlay:

```sh
ssh -o BatchMode=yes dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo/run_component_cover_nuc.sh /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo CoveredOriginalSymbols covered-original-symbols-nuc-v1'
ssh -o BatchMode=yes dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo/run_component_cover_nuc.sh /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo CoveredOODGRS covered-ood-grs-nuc-v4'
```

Lean 4.32.0 used `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0 and CPUQuota 200%. The respective green pre/postflight
inventories contain 703 and 709 artifacts, unchanged across each check.
Research source pin is stated above; borrowed source pin is
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, with Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. The native package-cache boundary
is pinned but package compilation itself was not replayed.

| Frozen artifact | SHA-256 |
|---|---|
| CoveredOriginalSymbols.lean | `446e4337224c6cc042ed13a09d7d42fcb482c89e4d45513ba7c8c036146ef5c7` |
| CoveredOriginalSymbols.olean | `08469f3c9e75a94cbf8310b2dde61a4003ba1a76c348794cb1dfa5791089eb46` |
| CoveredOODGRS.lean | `d1bb083cb127760ae242c0077f24d2862912f307ebc00181afa2bb35b435eb22` |
| CoveredOODGRS.olean | `bafe3e8e577913348173607edaabb450e90f1fd2bdf162a35cdfe747927360eb` |
| Shared NUC runner | `3ca08461281d836d1898786dcdb2a074089dbe89421f46b9eb81e35ac255f129` |
| Symbol-support green manifest | `ed3e0e5564956bcd3109eb96710ec11d1d1728c6f1fbbd9760262e1b93d2ce59` |
| OOD GRS green manifest | `979f532d98240e9c135b38bcbea9fdcc9c4438b018263b28ca5978bb71d32a79` |

Read-only source audit hashes at the research pin:

| Source path | SHA-256 |
|---|---|
| `crates/aspis-core/src/circle.rs` | `8f6f0f32c8dd93e3ee459df0c1d0ef710b01996d3bc929dbeffb3f7d14a0227c` |
| `crates/aspis-core/src/transcript.rs` | `be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119` |
| `experiments/inactive_row_binding.rs` | `4642f1e4361aeb9f991ef917f8efdea292187fe3de9e3a9d351230859f9ad98b` |
| `AspisFormal/AspisFormal/K1/V7Tag73SecureCircleMap.lean` | `6b3497ca6a87bbb87f71653a25a419745b65123eec769156ff33ba6cd2669070` |
