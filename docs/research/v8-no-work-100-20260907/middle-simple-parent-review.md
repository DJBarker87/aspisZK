# Multiplicity-one middle-only auxiliary parent

Status: five leaves are kernel-checked: `MiddleSimpleInterpolationV2` (five
audits), `MiddleSimpleRootV7` (eight), `SelectedMiddleSimpleParent` (six),
`MiddleLinearClassification` (two), and `SelectedMiddleGammaCover` (four),
all standard-only. The selected gamma capture is complete: outside one
pre-OOD pair-root event, the entire actual middle/high gamma set has at most
117145 elements. The exact OOD sampler law and global acceptance/probability
composition are separate consumers, not assumptions silently discharged here.

## Analysis-only selector change

`SelectedOODGate.fixedInterpolant` is a noncomputable choice from the
nonzero interpolation kernel. Its inputs are C1 and C2 only. It is not sent
on the wire, used by the verifier, or an executable extractor. Replacing
the choice with a minimizer of a natural-valued analysis objective would
preserve causality, provided the new choice is fixed from those same inputs
and its kernel/nonzero properties are proved. It would not by itself prove
any improved degree bound.

Within the old multiplicity-three space (X bound 114688, Y rows 112), the
literal dimension inequality gives a nonzero solution already at Z bound
35630, hence Y/Z weight at most 35629. The two relevant sums are
`sum_j(114688-1024*j)=6479872` and
`sum_j j*(114688-1024*j)=239755264`, for j=0..111. Thus
`6479872*z-28*239755264 > 6*1048576*z` first holds at z=35630.
This only certifies regular-factor cost at most 72,875,275, not the roughly
26,631,546 cost needed for the proposed middle-union cap. At the old Z bound,
the first Y-row truncation certified by this dimension test is 97 rows
(Y-degree at most 96). These are limits of that **dimension certificate**,
not lower bounds on the true minimum of the source-specific kernel.

The substantive new route instead leaves the old selector intact and adds a
second auxiliary parent for the stronger middle-support event. This changes
neither protocol nor source. The old parent remains available for the final
coherent-higher-factor intersection.

## Exact new parameter calculation

An image-valid quotient with at least 200808 whole fibres has at least
`4*200808-2 = 803230` original symbols, by the checked two-symbol pole-loss
bridge `SelectedRegularLowSupport.fibre_to_original_support`. Let

```
maximumDegree = 1024
curveDegree   = 28
xBound        = 803230
yRows         = 2
zBound        = 41.
```

Use only the zeroth Hasse condition. Its codomain has
`1048576*41 = 42991616` scalar entries. The coefficient count is

```
803230*41 + (803230-1024)*(41-28) = 43361108,
```

exceeding the codomain by 369492. No independence or full-rank assumption is
needed: dimension alone gives a nonzero kernel vector for every fixed
received 29-lane array. The code proves the count using a symbolic two-row
formula, not enumeration of the 43-million-entry domain or matrix.

The resulting parent has Y-degree at most one, X-degree at most 803229, and
weighted Y/Z degree at most 40. Every supported original candidate has GRS
degree at most 1024. Its substitution into the parent has X-degree at most
803229 and at least 803230 distinct roots, so it vanishes identically.
Candidate selection may be arbitrary after gamma, kappa, tau and alpha.
There is no assumed candidate curve, component tuple, or received-word
polynomiality.

## New source interfaces and status

* `MiddleSimpleInterpolationV2.simpleMap` selects Hasse (0,0) from the
  existing `curveInterpolationMap`; `exists_nonzero_simple_kernel` uses the
  smaller codomain. `constraint_zero` proves its identity in gamma.
  `middle_dimension` and `exists_middle_interpolant` are also checked.
* `MiddleSimpleRootV7.candidate_substitute_zero` / `candidate_root` reuse
  the exact weighted substitution degree and zeroth-evaluation identities.
  `middle_root` fixes the threshold. Parent nonzero/Y/X/weight bounds and
  the generic `positive_factor_linear_of_parent` are checked. The unused
  concrete-coefficient convenience wrapper was removed after focused
  elaboration failures; no consumer needs it.
* `SelectedMiddleSimpleParent.coefficients` chooses from the exact normalized
  `received29 c1 c2` array. `middle_original_support` and `candidate_root`
  preserve the same actual Q and the literal GRS multiplier normalization.
  This selected adapter is checked, including the same-Q root conclusion.
* `MiddleLinearClassification.exists_classification` constructs the
  pre-OOD E, the at-most-one fixed tuple family, sparse set, and shared
  post-OOD/pre-gamma exception. It is checked, with no additional root or
  candidate-membership assumption beyond its explicit generic inputs.
* `SelectedMiddleGammaCover` is the checked final selected consumer into
  the independently checked `MiddleGammaUnion`. It also proves the exact
  full/bad-fibre partition needed to map the actual `HighPrefix` witness.

The parent is chosen from C1/C2 before either OOD point/answer and before
gamma. Point claims, OOD answers, gamma and the post-alpha final are not
selector inputs. The auxiliary root does not replace or erase the actual
old higher-factor root: the same reconstructed original message supplies
both when the original event holds.

## Exact checked exception composition

The checked selected adapter now composes this chain:

1. `FactorIdentityCover.exists_identity_factor_cover` supplies one
   nonzero gamma polynomial of degree at most 40 after the completed OOD
   prefix. Its shared budget already includes zero specialization,
   Y-constant content and non-retained factors. Do **not** add a second
   40-gamma zero-specialization charge.
2. Every retained positive-Y prime factor of the new parent is linear.
   `LinearDenominatorFactors.exists_parent_obstruction` supplies a single
   pre-OOD E of degree at most `(2*40+1)*803229 = 65061549`. Away from the
   event where **both** actual OOD points are roots of E, every retained
   linear factor is small in gamma. This is a separate pair-root event;
   there is no probability claim without the appropriate point-draw law.
3. `LinearMessageFamily.family_card` is at most one and
   `sparseChallenges_card` is at most 28 for this parent. The family consists
   of actual 1024-coordinate message tuples; it is fixed before OOD/gamma.
4. For its at-most-one tuple, the actual OLD higher-factor condition puts
   the same original candidate in
   `EarlyC1HigherYSupport.Generic.coherentHits`. The checked
   `coherent_parent_count` charges at most 117077 over the old prime-factor
   family, including its multiplicities, with no factor-count multiplier.

Thus the non-pair-root middle union is at most
`40+28+117077 = 117145`, well below 34810510. The generic union and linear
classification are consumed by the checked final source-shaped capture.
Its `middleGammas` set existentially ranges over all old prime factors of
Y-degree at least three and all SAME-Q `Qualified` witnesses with at least
200808 full fibres. It does not restrict the old factor to regular or even
retained factors; the actual higher-prefix event supplies stronger facts.
`high_prefix_mem` maps the actual `HighPrefix`, with its selected adaptive
final, directly into that set. The exact full/bad partition derives the
threshold from the existing bad-fibre allowance; the older one-sided
inequality would not have sufficed for this direction.

`exists_selected_cover` quantifies E before all completed OOD data, then
proves either both actual OOD points are roots of that SAME E or the whole
gamma set has cardinality at most 117145. A mass consumer must use this E;
it cannot silently identify two independent existential choices. Gamma
remains the original domain, without acceptance or root-complement conditioning.
The theorem does not need
`earlyC1=none` or an own-support premise. In particular,
`earlyC1=none -> every tuple has own support<38228` is **not** asserted.
No shared suffix repair or query probability is charged per family member;
the later acceptance partition must attach the existing shared suffix once.

## Focused predecessor evidence

Both exact source snapshots/logs/manifests are retained locally. The first
attempt, tag `middle-simple-interpolation-v1`, failed solely at the generic
finrank cast seam; other statements were already standard-only. V2 adds
`norm_cast` before the existing symbolic ring step, with no changed theorem,
resource limit or enumeration.

| Target / tag | Exit | Wall | RSS (KiB) | Swap | Audits |
| --- | --- | --- | --- | --- | --- |
| MiddleSimpleInterpolation / middle-simple-interpolation-v1 | 1 | 3.04 s | 6800784 | 0 | Failed result, cascading sorryAx not accepted. |
| MiddleSimpleInterpolationV2 / middle-simple-v2 | 0 | 3.12 s | 6833848 | 0 | 5; only propext, Classical.choice, Quot.sound. |

V2 source/snapshot:
`6b3f382aac1d7e843c49b0a4960f151925f7d41e483baae4056ffae8939773f2`.
Local output, independently matched to the NUC digest:
`294c224b291d058f3ae0223e0e44939f336308497ca677682bc6ea59ef92af78`.
V2 log `3a890896ed0f0972b0b3a44d2768423f35db88dab3076b25390945eef224464a`;
manifest `78d03dcb24e674e01925973c81c6662c7a96ac392f23930e8c21a49f1a7af72f`.
V1 source `7cb7979f25e3cd0e3d32a10959bdcf9436e6cb0692b024f70e8a374aec7b5f35`;
log `bafc6fc32e400832052baafe9f90fef986386cf147ad038ffd92352b15b673dc`;
manifest `116047f5b30d55f490802d05f196e2d1f00a7151da9823066cdb9742d6976a70`.

All seven root attempts have exact source snapshots, logs and import
manifests retained locally. V1's final concrete factor-degree wrapper hit
recursion depth 200; V2 extracted the generic parent-abstract lemma, but the
unused concrete wrapper still failed. V3–V5 were failed option/doc-comment
syntax variations, with the exact errors retained; V6 parsed the narrow
depth-512 option but still failed at that wrapper. V7 deletes only the
unused concrete wrapper and retains the eight needed declarations, all at
module recursion depth 200. Failed/cascading audits receive no green credit.

| Target / tag | Exit | Wall | RSS (KiB) | Swap | Result |
| --- | --- | --- | --- | --- | --- |
| MiddleSimpleRoot / middle-simple-root-v1 | 1 | 2.81 s | 6797388 | 0 | Final wrapper recursion failure. |
| MiddleSimpleRootV2 / middle-simple-root-v2 | 1 | 2.79 s | 6797452 | 0 | Generic helper passes; concrete wrapper fails. |
| MiddleSimpleRootV3 / middle-simple-root-v3 | 1 | 2.75 s | 6799708 | 0 | Option/doc-comment syntax failure. |
| MiddleSimpleRootV4 / middle-simple-root-v4 | 1 | 2.74 s | 6799360 | 0 | Option/doc-comment syntax failure. |
| MiddleSimpleRootV5 / middle-simple-root-v5 | 1 | 2.80 s | 6798984 | 0 | Doc-comment preceding option failure. |
| MiddleSimpleRootV6 / middle-simple-root-v6 | 1 | 2.88 s | 6799440 | 0 | Concrete wrapper recursion failure. |
| MiddleSimpleRootV7 / middle-simple-root-v7 | 0 | 2.98 s | 6832004 | 0 | Eight standard-only audits. |
| SelectedMiddleSimpleParent / selected-middle-simple-parent-v1 | 0 | 3.27 s | 6867220 | 0 | Six standard-only audits. |
| MiddleLinearClassification / middle-linear-classification-v1 | 0 | 3.11 s | 6861760 | 0 | Two standard-only audits. |
| SelectedMiddleGammaCover / selected-middle-gamma-cover-v1 | 0 | 4.21 s | 6878008 | 0 | Four standard-only audits. |

Root V7 source/snapshot:
`ea9c23689ae1aea1229f367a4ef3fd57e00e7e79746fa585d46f6bf62888f798`;
output `0c809759b6d55e5a59b63f81e5f3fd2a8363bc12d2888a5dbb00c184af595c53`;
log `4cfe740f2b5faf934ba784e6684a56207cf5b6b2f96ca4073c68ff1a97847706`;
manifest `c429963a6f34a534d314cfd9f7031d8cf4a2e8fed2cf9d81a06ba3c1b2b5a692`.

Selected parent source/snapshot:
`be106ac01be722ad520b95e54bbd5f91e38f7a54e36b0809f7dd2eef03ca5379`;
output `b92a716435f61487944ac557573cd1bde33e8e3ac6b82c761909fc7f4bcd5f73`;
log `e2ab83c309ad52e9b88114571e6cc3f9fdb6beb769866c14823dae7724c7bff5`;
manifest `7df8bdbbe6f1f6d3b46d3e2cf7b7bb5f614183703767c5b6dac661863edd858b`.

Classification source/snapshot:
`49dad128b69573490705671b7c0d7d6e8f7fb26009e5cb37b5e68259528b4f97`;
output `fadf61d7dacadbfbe35c97de1203a43c6f48fd353b803e17904260755992ebd8`;
log `abb448e250bef61a15699913862e45ff3eb90a291e3e87292f1edc7b26bb0ea7`;
manifest `1e4c3b630dc087030c37d664504b54ed261668760f5dd5e20e1da0f18c32b717`.

Final selected cover source/snapshot:
`37bb6e5e473ea70c8ed79e7b1b3ffd3eea2f44178c2ff8c29dfd09e7e68978fa`;
output `51dcfd40253387e8605dfd3075e74864a539cf0677ca2ac2d19111341383a4d9`;
log `ee12253882eb4796fa2752a2aef1583f8bba2c6526c354dc0c7eaf559524d4c5`;
manifest `13b4f8ee3d720116dc8a539c8024af11b0a8c9d21b5ba2b8b46d6f7ad449acb0`.

The owned census is five green leaves, 25 standard-only audits, 12 exact
attempt triplets (five successful, seven failed). Every attempt used zero
swap. All green source snapshots and current output digests match locally.
The independent `MiddleGammaUnion` is a checked dependency, not counted
again among these owned leaves.

All Lean jobs were coordinator-run on Tailscale
`dombarker@100.108.41.90`, inherited task `aspis-higher-y.fMoMeX`, Lean 4.32.0,
`-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB, SwapMax 0, CPU 200%.
V2 interpolation records 1021 registered entries unchanged before/after;
root V7 records 1025, selected parent 1027, classification 1029, and final
capture 1031. These
are registered-byte provenance checks, not claims to replay every import;
native package compilation was not replayed. Runner creation pin remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, borrowed pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, distinct from the current source
continuation (source work HEAD `f08d22d0e702b5b2b23a3bad8a66ff5bf653d64c`).
No local Lean build or matrix construction was run.
