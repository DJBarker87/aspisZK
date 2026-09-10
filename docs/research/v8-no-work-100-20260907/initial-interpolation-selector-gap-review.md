# The initial interpolation kernel is not projectively unique

Checked proof: [InitialInterpolationKernelDimensionV2.lean](experiments/InitialInterpolationKernelDimensionV2.lean).
The focused NUC V2 check is green, with five standard-only axiom audits.
Source SHA256 `3bc730d47549c2dc70bbcd6858935cb9936b4ae478c448fe15d03359aa400106`.
The failed V1 source is preserved separately, not overwritten.

## Exact source obstruction

[`SelectedOODGate.fixedInterpolant`](experiments/SelectedOODGate.lean) is
`Classical.choose (exists_exactInitialCurveInterpolation (received29 c1 c2))`.
The exported specification gives nonzero coefficients and membership in the
interpolation kernel. It does not select a minimum-degree or normalized
generator.

The pinned V7
[`exactInitialCurveInterpolationBudget`](../../../AspisFormal/AspisFormal/K1/V7ExactCorrelatedAgreementInterpolation.lean)
already certifies the following dimensions:

| Space | Dimension over K |
|---|---:|
| Allowed coefficient vectors | 751937306624 |
| Allocated Hasse-constraint outputs | 736591085568 |
| Difference | **15346221056** |

The domain is
`CurveMonomialIndex 1024 28 114688 112 117078 → K`.
The codomain is `Fin 1048576 → Fin 6 → Fin 117078 → K`.
The source deliberately overallocates some output slots. Dependent or unused
constraints can only increase the kernel dimension, not decrease this bound.

For **every** choice of points and received lanes, rank-nullity gives

`15346221056 ≤ finrank K (ker (curveInterpolationMap points lanes))`.

Thus projective dimension one is impossible in the literal selected system,
not merely unsupported in a toy example. For any chosen kernel vector there
is another kernel vector outside its scalar span; that other vector is
necessarily nonzero. This remains true for the actual chosen vector after
applying its existing kernel specification. There is no need to know its
coefficients or enumerate the field.

Nonassociation by itself does not prove that a particular factor is absent
from some kernel member: distinct polynomials can share factors. It rules
out the proposed argument that all nonzero choices are associated and hence
have identical factors. A separate common-factor theorem would need proof.

## Exact factor-changing countermodel

The [checked executable control](empty-early-family-kernel-control-review.md)
has two explicit nonzero kernel members, with δ=Z−1 and B the bad-point
locator:

`P_hi = (Y^31−Y−X³(δ^31−δ))³ B³`,

`P_lo = (Y−δX³)³ B³`.

At good coordinates `Y=δx³`, both indicated factors vanish identically in Z;
at bad coordinates B vanishes. Cubing gives all multiplicity-three Hasse
conditions. Both parents fit the same allowed monomial region: P_hi has
X+2Y weight 222 and Z+28Y weight 2604, while P_lo has the smaller bounds
45 and 84. Their Y degrees are 93 and 3, so they cannot be scalar multiples.

The irreducible degree-31 factor of P_hi cannot divide P_lo, whose entire
Y degree is only 3. P_lo has only the indicated linear-Y factor and
zero-Y locator factors. Both parents have the same two polynomial OOD
identities (answers 0 at X=0 and δ at X=1), and the same high-support
candidate U=0 at gamma=1. This explicitly shows factor membership changing
with the permitted kernel choice in the synthetic model.

P_hi's 528 symbolic Hasse constraints were checked by the frozen executable.
The P_lo statement here follows directly from its displayed vanishing
factor and the same cube argument; no extra executable run is represented
as having checked it. The countermodel's literal-circle, actual parameter
and fixed-selector limitations remain exactly as documented in that review.

Even imposing both parent OOD identities would not plausibly recover a
one-dimensional linear system: for fixed degree-at-most-28 answer curves,
each adds at most 117078 scalar linear constraints on these coefficients.
The resulting rank-nullity lower bound is still 15345986900. This is a
dimension observation, not an additional theorem of the current draft;
it says nothing about nonlinear candidate/row restrictions.

## Small proof and dependency map

The new leaf imports only the already pinned
`AspisFormal.K1.V7ExactCorrelatedAgreementInterpolation` and uses:

- Mathlib `LinearMap.finrank_range_add_finrank_ker` and
  `Submodule.finrank_le` for the symbolic inequality;
- `Module.finrank_pi`, `curveMonomialIndex_card` and the existing symbolic
  codomain cardinal calculation;
- the existing `exactInitialCurveInterpolationBudget`, consumed by rewriting
  its two dimension equalities, followed by natural-number linear arithmetic;
- `finrank_le_one_iff` to rule out a single generator for the kernel.

The five checked declarations are `nullity_lower_bound`,
`not_all_kernel_scalar`, `curve_nullity_lower_bound`,
`initial_kernel_dimension` and `initial_not_projective_unique`.
The source sets recursion depth 200 and heartbeats 200000. It does not
normalize the monomial count, reconstruct the enormous matrix, replay the
V7 numeral certificate or import the wider causal game.

The selector gap therefore remains, with a decisive reason the proposed
projective-uniqueness repair cannot close it. A genuinely different repair
would need either a proved property common to every allowed kernel member,
or a separately specified useful selector and proofs reconnecting all its
consumers. Neither a convenient exhibited kernel member nor a change of
`Classical.choose` witness identifies the current literal selected parent.

No probability, extraction, payment, sampler, byte or CU claim follows from
this rank calculation. Existing frozen sources and the earlier executable
evidence are unchanged.

## Focused proof evidence

Parent ran the two focused targets in the inherited higher-Y NUC workspace
over Tailscale. Source preparation was on research parent
`2f012db3288c902f43659afb2e3137d15008597b`; the unchanged runner/cache pins are
research `289d7356c78a4cd493fe61a54f9548f2a0c11298`, borrowed V7
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`, Lean 4.32.0.
Both checks used MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPU 200%, `-j1 -M9500`; no package or numeral-certificate replay occurred.

| Target | Exit | Wall | Peak RSS KiB | Swaps | Outcome |
|---|---:|---:|---:|---:|---|
| `InitialInterpolationKernelDimension` V1 | 1 | 3.19 s | 6797900 | 0 | Codomain natural-number cast normalization failed; first two audits clean |
| `InitialInterpolationKernelDimensionV2` V2 | 0 | 3.31 s | 6830428 | 0 | Five audits, each only `propext`, `Classical.choice`, `Quot.sound` |

V2 adds only `norm_cast` between the symbolic codomain simplification and
`ring`, matching the existing V7 dimension proof. No cap was increased.
The unused `[FiniteDimensional K W]` warning in the generic scalar-span lemma
is retained and does not change the result. V1 preflight checked 1017 entries;
V2 pre/postflight checked the same 1019 provenance entries and reported
`PROVENANCE_UNCHANGED=true`.

V1 [source](experiments/initial-interpolation-kernel-dimension-v1-source.txt),
[log](experiments/initial-interpolation-kernel-dimension-v1.log),
[manifest](experiments/initial-interpolation-kernel-dimension-v1-manifest.json):

- Source: `209fe213399b51adc6e7ee84bdc7a56efc864cd7ec4ee63cad33a92c52ff63ea`.
- Log: `7df3c1ba231167133a938e8618aa8cb349decad35afbf5176af3e5cdd1c00289`.
- Manifest: `899197229a87f598a6d8700957a3ad0cb723eb4f24e14c7282b1ffca30b7939c`.

V2 [source](experiments/initial-interpolation-kernel-dimension-v2-source.txt),
[log](experiments/initial-interpolation-kernel-dimension-v2.log),
[manifest](experiments/initial-interpolation-kernel-dimension-v2-manifest.json):

- Source: `3bc730d47549c2dc70bbcd6858935cb9936b4ae478c448fe15d03359aa400106`.
- Log: `2fd2c5a3ad27fe54d69da2a4268bb74e8ea7be3b5d3f60794e956be01123ac45`.
- Manifest: `c3774ef8e78b6ff14d7c80d795a255ce010dd756b4f6883b81e4c14dce86e53e`.
- Olean: `5eb577e07a8580c12c9b1f132fa74dab7705c55dc429877f38a0e73e6abeee5c`.

Both attempt triplets and the green olean have been copied locally. The
checked source bytes are frozen; this is kernel-dimension evidence, not a
proof of any candidate-recovery or factor-selection property.
