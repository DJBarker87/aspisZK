# Finite middle-gamma union closure

Checked proof: [MiddleGammaUnion.lean](experiments/MiddleGammaUnion.lean),
SHA256 `db7abd6461c10c13fd01524b49da499af2e37f9a2f0026cd006567b9cb53799c`.
The focused NUC V1 check is green, with five standard-only axiom audits.

## Exact theorem and fixing order

Keep the **old** multiplicity-three parent P, fixed from C1/C2 before OOD.
Let C be a fixed finite family of curves of gamma degree at most 28, with
cardinality at most one. The separate new multiplicity-one parent/source
adapter must construct this family; it is not reconstructed separately at
each realized gamma by this counting lemma.

For p∈C, let H_p contain the gammas where **some** prime factor F of the
old P has Y degree at least three and vanishes on the curve p at that gamma.
Factors may repeat in the old multiset and may vary with gamma. The reused
`EarlyC1HigherYSupport.Generic.coherent_parent_count` proves

`|H_p| ≤ weight_28(P) ≤ 117077`.

The new `coherent_family_count` derives

`|⋃p∈C H_p| ≤ |C| weight_28(P) ≤ 117077`.

There is no factor-count multiplier and no union over an unbounded universe
of possible tuples. An empty family is handled normally by the empty union.

Let J be the actual hit-gamma set, B the shared new-parent exception set and
S the new-parent sparse set, with `|B|≤40` and `|S|≤28`. Given the source
capture implication

`gamma∈J → gamma∈B ∨ gamma∈S ∨ ∃p∈C, gamma∈H_p`,

`captured_union_card` explicitly proves
`J ⊆ B ∪ (S ∪ ⋃p∈C H_p)` and applies ordinary union bounds. No disjointness
is assumed: overlaps only make the bound smaller. If a disjoint partition is
desired, the same cases are `J∩B`, `(J\B)∩S` and `J\(B∪S)`; the theorem
does not need to manufacture or count that partition separately.

The exact arithmetic endpoint `middle_card` is

`|J| ≤ 40+28+117077 = 117145`.

## Pair-root alternative and remaining source premise

`pair_root_or_middle_card` returns

`E(t0)=0 ∧ E(t1)=0  OR  |J|≤117145`,

provided capture holds outside that pair-root event. It neither counts nor
averages the OOD event. Construction of a fixed nonzero E and its degree
bound (proposed 65061549) belong to the auxiliary-parent source adapter.
No independence of OOD labels or challenges is assumed.

The adapter must still derive B, S, C and the capture implication for the
**same actual original Q** used by the old higher-factor witness. In
particular:

- The new parent's at least 803230 matching symbols must give its literal
  specialized root and both actual OOD values.
- The shared degree-40 factor-identity exception should already handle
  content/zero specialization and excluded factors. Do not add an identical
  specialization exception a second time.
- The new parent's Y degree at most one must supply `|C|≤1` and `|S|≤28`.
- Outside B and S, the recovered curve must equal that same original Q;
  this equality transports its old higher-factor root into H_p.

Once those source facts hold, J may quantify arbitrary later kappa, tau,
alpha, final selections, Q and factor witnesses. The finite proof does not
freeze any such choice: only the covering curve family is fixed before the
charged gamma. No early-C1, regularity, own-support, payment or sampler
premise appears. In particular, `earlyC1=none` must not be mistaken for
absence of a weak early-family member; this argument does not use that
incorrect implication.

The original Gamma is supplied unchanged to every coherent hit set. If J is
defined by filtering it, the usual uniform finite-law conversion can later
give `117145/|Gamma|`; this leaf does not resample Gamma outside B or S.
The shared suffix repair, outer history averages and any pre-existing old
factor-cover exception remain separate global accounting steps. No extra
suffix repair is charged by this cardinality lemma.

## Proof dependencies and proposed check

The sole import is the green `EarlyC1HigherYSupport`. The new proof uses its
generic `coherentHits` and `coherent_parent_count`, the old
`curvePrimeFactors`/`trivariateYZWeight` interfaces, and Mathlib's finite
union/cardinality monotonicity. The only numerical calculation is the small
natural-number sum above; no field, code domain or interpolation matrix is
enumerated.

Declared targets: `mem_familyHits`, `coherent_family_count`,
`captured_union_card`, `middle_card`, `pair_root_or_middle_card`.
Recursion depth 200, heartbeats 200000. The checked source is frozen.
The finite union is proved; full source gamma closure still requires the
separate capture adapter described above.

## Frozen focused evidence

Source parent: `f08d22d0e702b5b2b23a3bad8a66ff5bf653d64c`.
Parent launched only `MiddleGammaUnion` using the existing higher-Y runner
over Tailscale, with inherited research/cache pin
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. Lean 4.32.0,
`-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPU 200%; no package replay.

Tag `middle-gamma-union-v1`: exit 0, wall 2.88 s, peak RSS 6866996 KiB,
swap 0. All five `#print axioms` lists contain only `propext`,
`Classical.choice`, `Quot.sound`; no warnings. Pre/postflight checked the
same 1023 entries and reported `PROVENANCE_UNCHANGED=true`. No retries.

- Source and [frozen snapshot](experiments/middle-gamma-union-v1-source.txt):
  `db7abd6461c10c13fd01524b49da499af2e37f9a2f0026cd006567b9cb53799c`.
- [Log](experiments/middle-gamma-union-v1.log):
  `98c73080a001c24db526502d8c639ebcf874242d9a07688fe5e56825565b6993`.
- [Manifest](experiments/middle-gamma-union-v1-manifest.json):
  `0e3480b5d67b793e228afba7072cfb87dc627e87e0b90846639865a541b43c86`.
- Olean: `7daf931b4e5ca6b7546157f921c1a19fa77612de4aec00cf74870964e2037519`.
- Frozen runner: `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

The complete attempt triplet and green olean were copied locally and their
hashes checked. No further source edits or builds are pending for this leaf.
