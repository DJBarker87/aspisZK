# High-agreement adaptive branches outside the fixed quotient family

This continuation proves a new support-averaging input and connects large
four-branch intersections to the actual selected quotient code. It does not
assume provider success or a preselected final, and it does not apply a
query union bound over candidate messages.

## Fixed family and exact residual event

Fix the received virtual word `R : Fin 1048576 → QM31` and selected fibre
domain D before alpha. Define

```
support_R(Q) = { i∈D | every one of Q's four encoded slots equals R there }
F_a(R) = { Q : Fin1024→QM31 | |support_R(Q)|≥a }.
```

This is the full natural quotient code, not the original/image-valid code.
The family depends only on R, D and a, not on the sampled alpha or chosen
final. It is a mathematical family; no algorithm, running time, cardinality
bound or payment-witness extractor is claimed for it.

For the actual alpha-adaptive final coefficient vector `final(alpha)`, use
the literal selected matching set

```
M_alpha = { i∈D | exactFinalLinear(final(alpha))(i)
                   = actualCanonicalCircleFold(alpha,R)(i) }.
```

`CoveredAt` means that **some** Q in F_a(R) has
`final(alpha)=coefficientFoldLayer 256 alpha Q`. The event `tailSet` means
`|M_alpha|≥t` and no such representation. Absence from this family is not
defined as failure of one decoder. Nor is represented membership already
a valid payment witness.

## New argument

Four distinct alpha branches with at least a>255 common matching fibres
construct Q through `four_selected_support_folds_recover`. That constructed
Q agrees on all four raw slots throughout the intersection, so it belongs
to F_a(R). The exact final-code overlap cap255 then identifies all four
adaptive finals with folds of Q. Thus any four off-family branches have
fewer than a common matching fibres. No shared support is supplied as a
premise: it is the actual intersection of their matching sets.

The old `NearGammaSupport.common_of_high_load` is too coarse at the new
density. `HighAgreementTail.lean` adds a symbolic discrete binomial tangent,
derived from Pascal telescoping and monotonicity:

```
choose(h,r+1) + m*choose(h,r)
  ≤ choose(m,r+1) + h*choose(h,r).
```

After summing, an average load of at least h yields
`sum_x choose(load_x,4) ≥ |D|*choose(h,4)`. The proof then reuses
`NearGammaSupport.subset_count` and exact double counting over four-subsets.

For 128 matching sets, each of size at least117,965, on262,144 fibres,
the average load exceeds57. The frozen certificate is

```
262144*choose(57,4)/choose(128,4)
  = 30818304/3175 ≈ 9706.5524 >9557.
```

Consequently some four have at least9558 common fibres. With a=9558, this
contradicts all128 branches being off-family. The checked selected endpoint
`selected_high_tail_card` therefore bounds
`tailSet(D,R,9558,117965,challenges,final).card` by127.
Both the universal support-averaging theorem and its actual selected-code
specialization have passed focused checks and standard-only axiom audits.

The certificate is reduced through four-term descending factorials. There
is no large concrete-field enumeration or Pascal-tree normalization.

## Applicability and accounting

This is genuinely new information about the high matching-count tail, not
another query-last identity. It applies uniformly to arbitrary fixed R and
arbitrary functions `final : alpha → Fin256→QM31`, so final selection after
alpha is preserved. The constructed Q can depend on the four hypothetical
branches; it is used only for a deterministic contradiction with membership
in an independently fixed family, not retrospectively frozen for a root
probability.

For a genuinely fresh ideal uniform alpha on a finite set A, cardinality127
corresponds to at most127/|A| for this precise high off-family event. The
actual source/challenge-law coupling and any larger probability composition
remain separate. There is no query-probability factor or candidate-count
union in the high-tail theorem itself.

Matching counts below117,965 and every represented branch remain outside
this bound. Their semantic/image/row classification, resource-bounded
recovery and payment validation are still required. In particular, an exact
invalid-image T512 quotient lies inside the family and is not rejected by
this result; the image gate remains necessary. The root-product and high-J
regressions are not discarded by relabelling them as failures of a radius
cutoff. No global q22 security certificate is asserted.

No verifier/protocol source, proof field, query count, body length or
production path changed. The body remains40,282 bytes. The selected leaf's
changed replay moved to the NUC; no CU measurement ran.

## Reproduction and evidence

Research revision: `b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9`.
Borrowed immutable V7/V5 closure: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
Concurrent main advanced read-only from `946ade6f86854c46b24a0291a5ce115749139a16`
to `e010ca133fbbec5cc48217d7b6dd7a3362350185`; required source bytes are
checked against the immutable pins, not current main declarations.

Historical laptop commands, retained to identify the recorded v1/v2 runs
(do not launch new laptop checks under the current host instruction):

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_high_agreement_tail.sh docs/research/v8-no-work-100-20260907/experiments/high-agreement-tail-replay.log
bash docs/research/v8-no-work-100-20260907/experiments/run_off_family_intersection.sh docs/research/v8-no-work-100-20260907/experiments/off-family-intersection-replay.log
```

Both use cached Lean4.32.0 via the `lake env` environment, `-M7000`, and a
serialized7-GiB aggregate child-RSS guard. No dependency/package replay ran.
The new NUC checks use the isolated staged overlay and `run_masked_nuc.sh`,
`-j1 -M6500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`; shared
cache sources and artifacts remain read-only.

| Leaf/replay | Exit | Lean wall | Peak RSS | Swaps | Status |
|---|---:|---:|---:|---:|---|
| HighAgreementTail v1 | 1 |12.82s|2,809,790,464B|0|Local Nat casts/closed-certificate specialization needed explicit normalization|
| HighAgreementTail v2 | 1 |9.80s|2,813,198,336B|0|Generic mathematics green; unnecessary no-progress simplification stopped fixed endpoint|
| HighAgreementTail v3 | 0 |12.79s|2,848,374,784B|0|All8 audits standard-only, full postflight passed|
| OffFamilyIntersection v1 | 1 |55.55s|4,285,153,280B|0|Constructed-family and off-family intersection lemmas green; final cardinal wrapper needed direct inequality transport|
| OffFamilyIntersection v2 | 1 |46.61s|4,850,155,520B|0|Direct application exposed filter-instance definitional recursion; no memory failure or cap increase|
| OffFamilyIntersection NUC v1 | 134 |3.55s|6,773,744KiB|0|Memory exception while loading the broad dependency closure, before declaration audits; not retried unchanged or with a higher cap|
| SelectedSupportIdentification NUC v1 | 134 |3.73s|6,766,252KiB|0|The PartialFoldSelected import closure still exhausted the same limit before declarations; narrowed again before retry|
| SelectedSupportIdentification NUC v2 | 0 |3.28s|6,824,612KiB|0|Canonical-encoder-only import; two standard-only audits and postflight passed|
| OffFamilyIntersection NUC v2 | 0 |3.10s|6,827,120KiB|0|All three selected theorems, including the127 cardinal ceiling, passed with standard-only audits and postflight|

Generic frozen SHA-256:

- Source: `740170c9447e45f6a18626332cfd873d7bfeb7ea52b46c85e9c44e700bc06db5`
- Olean: `ae4194137cd026c25ce4bd1c8cfc3a8efccf538e71cafc6c8a39924934aafaa0`
- Runner: `32d8505795ae385eb19458f1035f4f0ae91b9f942348f7c2aa0978e29cb104d7`

The selected source-only correction replaces definitional identification of
the two filter cardinalities with explicit finite-set extensionality and
opaque Nat arithmetic. Its replay moves to the NUC following the user's
host change; no further laptop compile is authorized or performed here.
The NUC import failure exposed an unnecessary dependency on
`SevenAlphaRecovery`: this counting leaf only needs its two geometric
encoder/support lemmas, not the causal relation game. The new, separately
checkable `SelectedSupportIdentification.lean` now imports only
`AspisFormal.K1.V7Tag73CanonicalOneFoldSchedule` and reproves those same two geometric statements from
the pinned V7 encoder commutation and final-code overlap theorem. The
committed seven-alpha source is untouched. `OffFamilyIntersection` now
imports this narrow helper and explicitly imports `PartialFoldSelected`
for the four-branch reconstruction theorem it actually uses. Its public
family/event definitions and mathematical conclusion are unchanged.

The first separated helper still exceeded the original NUC heap limit while
loading dependencies. After inspection of that native import-time baseline,
the build coordinator authorized the further-narrowed helper and dependent
at `MemoryMax=10G`, `-M9500`, still with swap disabled and no overlapping
build. This was a changed-source/import retry following a recorded review,
not an unchanged retry or a larger concrete-normalization allowance. The
smallest helper passed first, then the dependent selected theorem. The
measured peaks were approximately6.51GiB for both, with zero swaps.

Frozen narrowed SHA-256:

- `SelectedSupportIdentification.lean`: `67a34cfe28ca5ac316714049e5293fac6e22e2d2de6752a2f283c58e0dde792d`
- `SelectedSupportIdentification.olean`: `9f6d715ae54a8cf163f69b1e6327db13d6f326a2fffe82e91a5fa2555b71efe9`
- `OffFamilyIntersection.lean`: `ca8929501650a5d9085b9d4b1b8cded4db6cf7feea1e0b5cf2e4648793f670c0`
- `OffFamilyIntersection.olean`: `f827df9891f6b70c488e279889c84def32b23043d51f0baf53e0381d08341a09`

Failed logs are retained and are not claimed proofs. Retained results must
audit only to `[propext, Classical.choice, Quot.sound]`, with no `sorry` or
new axiom.
