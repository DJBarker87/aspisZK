# Exact global folds: a smaller arbitrary-word residual

Research continuation from `33e13de4e4b8bfdef7f3f2fb2e472b34db44865e`.
Main inspected read-only at `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
No production, main, parameter, wire, or verifier changes in this subtask.

**Status:** both the generic arbitrary-word recovery theorem and the exact
selected-encoder specialization are kernel checked. The finite F17 control
passed. This closes the globally exact-fold subcase of the non-polynomial
received-word problem, not partial agreement or global payment recovery.

## What the latest V7 candidate-directed work does, and does not, provide

The four latest `V7Tag73K13CandidateDirected*` files are **untracked main
work**, not imported as established dependencies here. They expose:

- The selected work/final/query-batch scheduler coordinate.
- A union covering the already-defined joint query-batch collision event by
  candidate/fold-trial/final-trial coordinates.
- A pointwise root target of at most 16 values for an already-chosen concrete
  collision witness.

The last target is chosen using the *complete sample and collision event*.
Its pointwise size alone is not a causal probability bound: the committed
`ExactTag73RestrictedK13JointBatchSource` still requires a pre-answer `view`
and its `covered` inclusion on the corresponding coordinate fibres. The
untracked trial cover does not construct that view or prove its constancy.
None of these declarations supplies a missing C1 candidate, repairs K14
width29 `none`, or bounds all accepted far branches. No q16/degree16 cap is
transplanted into V8's q22/degree22 shifted batch.

The committed `V7CandidateChainExtraction.accepted_selects_one_consistent_chain`
is reusable as finite-chain logic only with its exact code/word model and its
explicit exclusions of query, one-fold and list-cap failures. Its
`ExactDecoderInstantiation` includes completeness and output-list bounds;
the 9,900 candidate-pair search bound is not a runtime bound for supplying
those lists or a C1/payment-witness extractor. K14 still has its separate
width29 decomposition failure.

There is a simple permanent obstruction to substituting the V8 matching set
into V7's raw-word `IdealAccepts` definition unchanged. Let the original word
be `U=1` and use its honest two-point interpolant `I=1`. Then `(U-I)/L=0`
for every legal nonzero chord denominator. V8's quotient fold agrees with
`final=0` everywhere; V7's raw fold of `U` is `1` for every alpha. The new
`raw_quotient_fold_separation` statement records this algebraic difference.
It is not a payment execution or forgery. A source bridge must use the
actual quotient and a corresponding full quotient code, not the old raw
gamma-batch word with the same disclosed final.

## New restricted recovery statement

Fix the actual received quotient word `R` before alpha. Let `E` be the fixed
linear final encoder, and use the actual circle-fold slot order
`(x,y),(x,-y),(-x,-y),(-x,y)` with checked inverse identities
`2*x*inv2x=1`, `2*y*inv2y=1`.

Define `W` to be the **full** radix-four circle lift of `E`:

```
W = range (circleLiftEncoder E x y).
```

This is not the smaller image-valid subset. No polynomial/image coefficients
are ascribed to an arbitrary received word.

The proved generic endpoint is:

> If there are four distinct alpha values for which the actual folded
> received word lies globally in `range E`, then `R ∈ W`.
>
> Consequently, for `R ∉ W`, at most three alpha values permit **any**
> globally matching final codeword, including a final chosen after alpha.

The proof does not assume the desired anchor or provider success. It uses
the existing exact arbitrary-word inverse `radix4Decode` to write the fold
as a cubic in alpha with four coefficient *words*. Four code-valued
evaluations interpolate those coefficient words inside the linear code.
They therefore have coefficient-message preimages. Packing these four
messages in the actual `4*parent+slot` order and applying the previously
proved inverse reconstructs `R` in `circleLiftEncoder E x y`.

The construction is mathematical: it chooses four good parameters and
coefficient-message preimages. This does not supply a resource-bounded
replay extractor that obtains those global codewords from q22 openings.
A Merkle root does not expose the received vector, and an accepted sampled
execution need not establish global equality. No provider `none` branch is
discarded by calling the constructed object an executable decoder.

| New declaration | Implication proved / consumed |
|---|---|
| `four_code_evaluations_recover_coefficients` | Four evaluations of a cubic word lie in a linear code ⇒ each coefficient word lies in that code |
| `foldCurve_eval_actual` | The cubic word is the existing normalized `circleFoldLayer`, not a newly assumed fold |
| `decoded_slots_in_range_reconstruct` | Four code coefficient words reconstruct all received slots in the lift |
| `four_exact_folds_recover_received` | Global exactness at four distinct alpha values ⇒ received membership |
| `adaptive_global_final_matches_le_three` | An adaptively chosen final is a subset of the existential globally code-valued event |
| `fullQuotient_iff_lift` | Selected log20 natural1024 membership equals the instantiated lift event |
| `four_selected_folds_recover`, `nonpolynomial_selected_challenges_le_three` | Concrete selected recovery/count endpoints, status recorded below |

This genuinely reuses V7/V5 algebra:

| Reused theorem/definition | Role |
|---|---|
| `circleFoldValue_eq_coefficientFoldValue_decode` | Exact cubic decomposition of arbitrary four-slot received values |
| `radix4Evaluate_radix4Decode` | Reconstruct arbitrary received slots under the actual inverse identities |
| `circleLiftEncoder`, `radix4LiftEncoder_apply_child` | Explicit full-code lift, not an assumed abstract membership bridge |
| `coefficientLane`, `parentIndex`, `slotIndex`, `childIndex` identities | Exact source-compatible natural coefficient packing |
| `monomialPolynomial` coefficient and degree theorems | Recover the four coefficient words from interpolation |
| `exactInitialEncoder_eq_circleLift` | Committed log20 natural1024 evaluator equals the log18 natural256 circle lift; used by the selected specialization |
| `canonical_one_fold_schedule_exact` | Committed nonzero-domain inverse tables, independent of alpha; no caller-supplied exact-inverse assumption |

The generic theorem has arbitrary dimensions. `ExactFoldSelected.lean`
specializes to `n=256`, `m=262144` using committed V7 mathematical encoder
identities, not the historical V5 log19 `encoder0/encoder1` sizes. The fixed
`exactFinalLinear` evaluates natural256 coefficients at `storedFirstLineX18`;
`exactInitialEncoder_eq_circleLift` identifies the complete stored log20
natural1024 circle evaluator with its lift. The canonical schedule at alpha
zero supplies the inverse arrays (the arrays themselves are independent of
alpha). This is an actual code/domain identification, not a requested
equality supplied as a hypothesis. The final encoder is fixed before alpha.

The remaining source distinction is important: these are the committed
mathematical encoders and `circleFoldLayer`, not a new Rust-to-Lean
translation of every branch of `opened_values_prepared`. The research
query source uses the matching four-slot order and final position
`2*x^2-1`, and its optimized/source-reference tests exist. A complete
translated-source/actual-prefix bridge is still separate.

## Causal and event interpretation

For ideal uniform full-field alpha, the non-code, globally matching event
has bound `3/k`, `k=(2^31-1)^4`, for the selected mathematical encoder.
Exactly, this is `3/21267647892944572736998860269687930881`, approximately
`2^-122.4150374966`. This probability interpretation is
the elementary uniform-counting corollary; the new endpoint is a Lean
finite-cardinality theorem, not an actual FS probability theorem.
The finite-cardinality theorem is pointwise in the complete pre-alpha prefix.
`R` may depend on earlier gamma/OOD/C2 information; it may not be redefined
after alpha. The final may depend on alpha and all earlier responses. A
relation reply chosen before alpha can be included in the fixed prefix.
Nothing here assumes all later relation replies are fixed early.

This gives the following restricted classification, not a complete security
sum:

| Actual received quotient | Further property | Existing/new obligation |
|---|---|---|
| `R ∈ W` | Reconstructed polynomial image invalid | Existing exact-polynomial joint image game, with its actual source interfaces |
| `R ∈ W` | Image valid | Reconstruction gives an original-code anchor; component/C1 recovery still uses the near-gamma and payment bridges, not batched membership alone |
| `R ∉ W` | Folded matching set is the entire final domain | New ≤3-alpha event |
| `R ∉ W` | Partial folded agreement | Still unresolved in general; may contain already-covered near cases and genuinely far/provider-none cases |

An arbitrary oracle does not acquire image coefficients by entering the
last two rows. The exact/global event is only one subevent of actual
acceptance; checking 22 queries does not establish global equality. For
matching counts below the full domain, even `T-1`, this theorem gives no new
agreement-tail bound. The accepted-extraction target remains `A AND NOT X`,
not `R ∉ W` or a radius cutoff. An out-of-radius execution that a legitimate
extractor successfully decodes still contributes zero to that failure event.

Do not add `3/k` blindly to the existing near/image bounds: image, near and
global-matching events require an actual causal partition, their source
interfaces and the four relation repairs must be charged once. The result
does not convert the old width29 error into a new numerator or prove that
partial-agreement candidates are covered. Authentication/source mismatch,
replay/fuel failures, C1 sampling/decoding, selected payment constraints,
full-view ZK and the resource-bounded FS lift remain separate.

## Exact small-code falsification control

`exact_fold_control.py` executes a predeclared F17 word on two disjoint
four-point circle fibres `(3,3)` and `(6,4)`; their final doubled-x positions
are distinct. The final code is the constant code on these two positions.
The first received fibre is zero, while the second is `[9,9,10,16]`.
Its decoded coefficient words give

```
Fold_alpha(R) = (0, (alpha-1)*(alpha-2)*(alpha-3)).
```

The inverse-matrix basis checks show that `R` is not in the full lifted
constant code. Exhausting all 17 alpha values and all 17 candidate finals
finds exactly three globally matching challenges: `1,2,3`, all with final
zero. Thus a proposed universal cap of two is false in this class, while
the cap of three is attained. The search is exhaustive over finals/alphas
for this one fixed word, not over all committed oracles or causal payment
strategies. It makes no small-field-to-QM31 rate extrapolation.

This is a tiny exact-integer preflight, under 0.1 second, not a dense field
elimination or proving benchmark. Output is retained as
`experiments/exact-fold-control-output.json`. No witness or secret data was
used or printed.

## Scope, provenance and focused proof evidence

The leaves only import the committed V7/V5 closure rooted at
`AspisFormal.V5FriConcreteEncoderApplicability` and
`AspisFormal.K1.V7Tag73CanonicalOneFoldSchedule`, checked against immutable
main `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. Every imported Aspis source
and cached olean is hashed before/after successful compilation. It imports
none of the untracked candidate-directed files. Their read-only audit
hashes were:

| Untracked file | SHA-256 at inspection (not proof evidence) |
|---|---|
| `V7Tag73K13CandidateDirectedCoordinateSelected.lean` | `cc5d2e6df23280ea59af42fb2c6b25a53cd6927bbcd313075ab7ba314566ed5c` |
| `V7Tag73K13CandidateDirectedPointwiseTarget.lean` | `616e51b1cac312ab2503bef33d3aeb4c5b59eccd268eb0d4270b210c96054e9b` |
| `V7Tag73K13CandidateDirectedTrialCover.lean` | `67f8be400d445e70a321a14e21318964362971e58eab91747ff87f17c3991fa7` |
| `V7Tag73K13CandidateDirectedTrialEvent.lean` | `9ac019cf42c10a029bc3c5ac861d71adae7f5eb81d8dc4561a676bf35d47aae8` |

The runner uses the existing Lean
4.32.0/Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` cache, `-M7000`,
and a serialized 7-GiB aggregate descendant RSS guard. No cap increases,
cold builds or unchanged full replays are authorized. Every failed local
preflight is retained; none hit the memory guard.

| Focused target / log | Exit | Wall seconds | Peak RSS bytes | Swap | Scope |
|---|---:|---:|---:|---:|---|
| Generic v1 | 1 | 6.09 | 5,504,614,400 | 0 | Local coefficient-sum/evaluation errors |
| Generic v2 | 1 | 5.75 | 5,506,187,264 | 0 | Four Fin4 numeral exponents not reduced |
| Generic v3 | 1 | 15.98 | 5,505,253,376 | 0 | `norm_num only` did not normalize those four casts |
| `ExactFoldRecovery.lean`, `exact-fold-recovery-v4.log` | 0 | 6.69 | 5,607,768,064 | 0 | Seven audited declarations; only `propext`, `Classical.choice`, `Quot.sound` |
| Selected v1 | 1 | 17.22 | 5,582,307,328 | 0 | Missing namespace for `circleLiftEncoder`; corrected without raising limits |
| `ExactFoldSelected.lean`, `exact-fold-selected-v2.log` | 0 | 5.85 | 5,712,691,200 | 0 | Four audited declarations; only `propext`, `Classical.choice`, `Quot.sound` |

The successful generic source SHA-256 is
`cec5a14467730d504a1d907a97171c629695a378266d701296c0d0206fbf64a6`;
its olean SHA-256 is
`a04a1ef54343ab2b884302a71883c1f789ff9dddd9b5dbb696b43406465dc7d6`.
The selected runner checks both before consuming the generic import.

Selected source SHA-256:
`e78c34a3881432d97ba38129faa412956f69a0a0b743a184895f5ce2f1da1214`;
selected olean SHA-256:
`23553988a172f1cacb78e66a2bc889b578eaf5c1714d524f0b97c2e2b6375e9c`.
The selected log records 231 distinct borrowed Aspis source modules and their
cached oleans, checked against the same immutable main commit before and
after the leaf. These dependencies were reused, not rebuilt. In particular:

| Reused source | Source SHA-256 | Cached olean SHA-256 |
|---|---|---|
| `V7Tag73ExactOneFoldEncoderBinding` | `fb3fd1166f3afea5c32e67469384cbee8e65b4228c0ed22b8c30bed6b782e4b8` | `1913f4cc787550a6050df988884cff2c7683498dffa5b04720419fe823728c57` |
| `V7Tag73CanonicalOneFoldSchedule` | `2c018c0b8cd1a5b61f1eb3dfe921b824202574d1189680412ace8738045786a0` | `61208913647e00eefa50201d2d3b6c312de40fe23f1bbe017b60380188e065c7` |

The retained Lean source was not changed after its successful replay. No
new axioms, `sorry`, concrete-field enumeration, memory-cap increase or
package replay was used. The failed v1/v2/v3 generic attempts are local
elaboration evidence, not retained claimed proofs.

```
python3 -B docs/research/v8-no-work-100-20260907/experiments/exact_fold_control.py
bash docs/research/v8-no-work-100-20260907/experiments/run_exact_fold_recovery.sh /absolute/NEW.log
bash docs/research/v8-no-work-100-20260907/experiments/run_exact_fold_recovery.sh /absolute/NEW-selected.log ExactFoldSelected
```

The proof body remains exactly 40,282 bytes. This mathematical recovery
reduction changes no transcript, verifier operation, CU, prover time, masks,
or privacy claim. The decisive next mathematical step is the remaining
**partial-agreement** received-word recovery problem with image/relation
constraints. The source step for using this particular bound is the actual
pre-alpha received-word/normalized-fold coupling to the selected mathematical
objects above, including fail-closed parsing and challenge timing.
