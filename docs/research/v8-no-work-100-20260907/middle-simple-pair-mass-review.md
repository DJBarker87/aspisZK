# Auxiliary middle-parent pair-root mass

Checked V4: [MiddleSimplePairMassV4.lean](experiments/MiddleSimplePairMassV4.lean),
SHA256 `75006b35426490f43ef308ff3bf1123e34b37917ae8ac1d46bc7023a9eeb6bf3`.
V4 is green with eight standard-only audits. V1–V3 failures are preserved.

The leaf reuses `LinearDenominatorFactors.exists_parent_obstruction 28` on
the actual `SelectedMiddleSimpleParent.parent c1 c2`. From its already
checked weight≤40 and X-degree≤803229, the obstruction E satisfies

`E≠0`, `degree(E)≤(2*40+1)*803229=65061549`.

Its full control statement is retained: every actual retained linear factor
of that parent is in the small recoverable class, or E vanishes at both OOD
points. The obstruction is selected from C1/C2 only, before either point;
answer polynomials may be chosen sequentially after their points and before
gamma. No received-word polynomiality or arbitrary candidate membership is
added.

## Complete root set and abort-preserving bound

`exists_complete_root_set E` constructs the complete set as

`univ.filter (fun t => Admissible t ∧ E.eval t=0)`.

The mass theorem takes the resulting S and its full membership equivalence,
avoiding unfolding the concrete QM31 universe in later proofs. S includes
every admissible root, not merely sampled roots. The polynomial
root bound gives its cardinality at most 65061549. Reusing
`RootSetPairMass.actual_one_call_target_bound`, the leaf bounds its ordered
distinct-parameter target mass by

`65061549*65061548 / (N*(N−1))`, where `N=P^4−P^2`, `P=2^31−1`.

This is the nested circle-three/distinct-three finite kernel. Ordinary
failure immediately has zero continuation; abort mass is retained, not
conditioned away. The ordinary atom mass is the checked actual decoder's
unconditional success mass divided by its field cardinality. The hypothesis
`NestedCircleMass.Generic.Uniform coins draw ordinaryAtomMass` must still
hold **at every history**. The arbitrary `between` history update after the
first point/answer remains in the theorem. No independence follows from
labels, and no Fiat–Shamir/ROM freshness is established.

The theorem is about the fixed admissible parameter root event in that
model. Connecting arbitrary `Data` coordinates to the actual sampled
parameters is not silently assumed by this arithmetic; source consumers
must use the checked parameter-inverse/source-coordinate interfaces.

## Same-E interface

The gamma classifier exposes its own existential E. It is invalid to
identify that E with a separately chosen `obstruction c1 c2` merely because
both arise from the same existence theorem.

For that reason, `pair_root_mass_numeric_le` accepts **any** fixed E≠0 of
degree at most 65061549. The final gamma consumer can pass the very E from
`SelectedMiddleGammaCover.exists_selected_cover` together with its degree
proof. `selected_pair_root_mass_numeric_le` is an additional concrete
instantiation on this leaf's canonical obstruction; it is not needed to
assert equality of the two choices.

The source import and finite root-set/mass statements contain no early-C1,
regularity, own-support or payment hypothesis. They do not charge the shared
suffix, any additional gamma exception or a second specialization error.
No new transcript byte or CU claim is made.

## Focused repair status

V1 source [MiddleSimplePairMass.lean](experiments/MiddleSimplePairMass.lean)
has SHA256 `f51ddb85e2ec0bf886eea6fb818f2f420cd0efbb26da327b6cf3fc352c7e6180`.
Its focused capped NUC check exited 1 after 2.94 s, peak RSS 6847500 KiB,
swap 0. The fixed obstruction and complete-root membership audits were
standard-only; the concrete root-cardinality and sampler callbacks hit
elaboration recursion depth 200. No mathematical failure was reported.

V2 preserves those arguments but first proves field-generic root-set
cardinality, a purely rational/Nat cap comparison, and the sampler bound
with an abstract finite set S before inserting the actual root filter.
Its callback conjunctions are explicitly typed. The module remains at
recursion depth 200 and heartbeats 200000; no memory or elaboration limit
was raised. V2 still hit the concrete-filter callback recursion seams and
one rational numeral representation mismatch: exit 1, 3.19 s, RSS 6854520
KiB, swap 0. V3 replaces the concrete-set function at the consumer boundary
with an arbitrary S plus its complete membership equivalence. All source
and root-set arguments then checked; only a rewrite of the final rational
constant failed: exit 1, 3.17 s, RSS 6853488 KiB, swap 0. V4 changes just
that last arithmetic step to a direct equality transport normalized by
`norm_num`; it does not unfold the field or domain size. All versions retain
depth 200 and heartbeats 200000. The V1–V3 source/log/manifest triplets have
been copied locally. No unchanged target or broad dependency replay was performed.

## Frozen proof evidence

Source parent: `f08d22d0e702b5b2b23a3bad8a66ff5bf653d64c`. Parent ran the
four focused targets over Tailscale in the existing higher-Y scope. The
inherited source/cache pin is `289d7356c78a4cd493fe61a54f9548f2a0c11298`,
borrowed V7 `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; Lean 4.32.0,
`-j1 -M9500`. Every attempt used MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0 and CPU 200%.

| Target | Exit | Wall | Peak RSS KiB | Swaps | Preflight |
|---|---:|---:|---:|---:|---:|
| `MiddleSimplePairMass` V1 | 1 | 2.94 s | 6847500 | 0 | 1031 |
| `MiddleSimplePairMassV2` V2 | 1 | 3.19 s | 6854520 | 0 | 1033 |
| `MiddleSimplePairMassV3` V3 | 1 | 3.17 s | 6853488 | 0 | 1033 |
| `MiddleSimplePairMassV4` V4 | 0 | 3.42 s | 6886612 | 0 | 1033 |

V4's postflight also checked 1033 entries and reported
`PROVENANCE_UNCHANGED=true`. All eight audits contain only `propext`,
`Classical.choice`, `Quot.sound`; no warnings. No limit was increased.
All four source/log/manifest triplets and the green olean are local and
hash-verified. Exact SHA256 inventory:

- V1 [source](experiments/middle-simple-pair-mass-v1-source.txt):
  `f51ddb85e2ec0bf886eea6fb818f2f420cd0efbb26da327b6cf3fc352c7e6180`;
  [log](experiments/middle-simple-pair-mass-v1.log):
  `d4d93bdeb3e83671f5fc561d339889e4655f2ab1f286caebd8af108491a93a07`;
  [manifest](experiments/middle-simple-pair-mass-v1-manifest.json):
  `6edc77a72e265f1e1e06da243637358ecca4ba0b6e2aa4d55ba7c2457c4c3e5a`.
- V2 [source](experiments/middle-simple-pair-mass-v2-source.txt):
  `1143a063404b767b81570fb813c57381c37e48948e399f3aa546ce7d656c900e`;
  [log](experiments/middle-simple-pair-mass-v2.log):
  `ce5cc74f54c11458df0609d1d5f261722a4d39e18c110062444728e345f4cb62`;
  [manifest](experiments/middle-simple-pair-mass-v2-manifest.json):
  `122e7178ecd80da3094e9dfae4502c0d0fa4c1747e9e74b2f4430cbfc2d63c23`.
- V3 [source](experiments/middle-simple-pair-mass-v3-source.txt):
  `5fc3b705a84f0191c297ec1192f4ad02a1d49fe96a0cc7131ee2a422797348ac`;
  [log](experiments/middle-simple-pair-mass-v3.log):
  `9bbd5d9e427cbb194c1d775c30d117f385f11a00b8940869dc7a532306384476`;
  [manifest](experiments/middle-simple-pair-mass-v3-manifest.json):
  `a1e3f4722f8ba9f6836fa0a672f8909b8bc518c3d972909cb49ef8cfc8e16274`.
- V4 [source](experiments/middle-simple-pair-mass-v4-source.txt):
  `75006b35426490f43ef308ff3bf1123e34b37917ae8ac1d46bc7023a9eeb6bf3`;
  [log](experiments/middle-simple-pair-mass-v4.log):
  `97ac2ccc5141733a9371eb45163e3919af1c841e766798cc0067fbb6b60b84b5`;
  [manifest](experiments/middle-simple-pair-mass-v4-manifest.json):
  `c35d72b7de45b989df19b48902b79d519e45dfb8a066845f362dc31d1047ff66`.
- Green olean:
  `657895071b918ed0ffa7d0fffd6dd933cdb9688a9e11088ad54cdc026737dde5`.
- Frozen runner:
  `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

The checked V4 source and this report are frozen. There is no further
theorem work planned beyond the requested gamma closure.
