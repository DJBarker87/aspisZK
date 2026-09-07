# Adaptive query-boundary review: a concrete query-only obstruction

2026-09-07. Research parent `1803896acf5d8c4ebe769b3927010031faf40e0e`.
The 40,282-byte allowance, selected production protocol and CU requirement are
unchanged. **No new upper bound on the actual accepted adaptive outside mass
has been established.** This continuation gives a specific obstruction to a
query-only bound, a source-event timing audit, and an exact high-agreement control.
It does not present another generic identity as a security repair.

## Outcome

The proposed query-last expectation and tail identity are correct in their
stated experiment. The supplied tests reproduce exactly. The pinned Mathlib
cache contains `Nat.sum_Icc_choose` in `Data/Nat/Choose/Sum.lean:130`; there was
no reason to spend another Lean development merely re-proving that identity.

The important new test fixes a base-field committed word **before either OOD
point**. It lies outside the original circle code, but its chord quotient
has a final256 representation with **perfect agreement on every query fibre**.
Consequently, in the algebraic oracle/chord/query model, if O means “no close
original component tuple”, then **H(T)=1** is possible. Query weighting alone
cannot eliminate that case. Its nonzero reconstruction/image residual must be
charged through an actual image/relation acceptance argument.

This is **not** a claim that the actual scheduler's H(T) is one, that the
literal K14 `width29` event has that tail, or that a complete payment proof
accepts. Earlier semantic checks, the image/relation checks, source correspondence
and the actual prefix distribution are not included in that algebraic model.
In particular, a condition excluding image errors cannot be silently imposed
and then treated as free conditional sampling.

## 1. Source-shaped events at the query boundary

Inspected the V8 worktree at `07b66afc22288a6ff460180242b73de4f341e02d`.
The existing definitions are in:

- `V6OneFoldCandidateExtraction.lean`: `consistencySet`, `QueryPhaseFailure`,
  `OneFoldReductionFailure`, `InitialListCapFailure`.
- `Pool/V7CandidateChainExtraction.lean`: `foldedReceived`, decoder-list
  filtering and `selectCandidateChain`.
- `Pool/V7CoherentTraceExtraction.lean:190`: `Width29DecompositionFailure`.
- `K1/V7Tag73ParsedK13K14Classifier.lean`: classifier order and errors.
- `K1/V8A100SchedulerNativeK14Provider.lean`: actual partial-provider wrapper.

There is a useful resolved timing point: **the mathematical K14 width29 event
is prefix-determined in the ideal full-oracle model**. Its arguments are decoder,
words, gamma, disclosedFinal and schedule. The schedule contains alpha and the
domain maps, not the query sample. The event does not inspect the queries or rho.
A proof of this measurability does not require efficient enumeration of its
decoder lists, and a Merkle root alone is not a revealed full oracle.

For the source's pointwise event P, define the following ordered classes:

| Class | Predicate / timing | What is available |
|---|---|---|
| Low agreement | M <= 9557 | Prefix-only; `QueryPhaseFailure = P AND Low` |
| Fold failure | M > 9557 and `OneFoldReductionFailure` | Prefix-only |
| List failure | Dense, no fold failure, `InitialListCapFailure` | Prefix-only |
| Width29 failure | Dense, no fold/list failure, `Width29DecompositionFailure` | Prefix-only; principal remaining component-recovery case |
| Covered | Remaining pointwise-accepted cases | Existing deterministic extraction inclusion |

Thus these mathematical classes can be organized before the queries rather
than equating the whole provider's `none` with a single new event. `idealRejected`
is the complement of P, not a prefix-only event. Replay abort/out-of-fuel,
response failure and gamma mismatch also require actual replay endpoint facts;
they are not all renamed to O. Restored/cached/advance correspondence remains
part of that source proof.

The necessary acceptance inclusion is still

```
actual accepted and unrecovered
  => source/authentication/replay error
     OR batch/later-relation error
     OR (pointwise accepted AND one of the prefix failure classes).
```

This is a definition/source audit and a mathematical organization of existing
inclusions, not a newly compiled complete q22 scheduler theorem. The existing
source theorem is q16 and folds the original word. **V8's quotient matching set
cannot simply be substituted into V7's `consistencySet`.** The quotient-to-original
reconstruction and relation bridge is essential, as the next construction shows.

## 2. A pre-OOD committed full-degree word

The selected original space is

```
W = { A(x)+y B(x) : deg A<=511, deg B<=511 }, x²+y²=1.
```

With z=x+i*y, it has Laurent support [-512,512] and endpoint coefficients whose
sum is zero. Fix one C1 column to

```
f(x)=T_512(x)=(z^512+z^-512)/2.
```

All other columns can be zero. Its values on the base circle domain are M31,
so this is not a noncanonical limb or mixed-field trick. The prototype tests
both semantic lane 0 and mask-only lane 25. The committed f is independent of
all OOD points, gamma, alpha and queries.

Every g in W has endpoint sum zero, whereas f has endpoint sum one. Therefore
z^512(f-g) is nonzero of degree at most 1024. It has at most 1024 distinct roots.
No g, even chosen adaptively after the challenges, agrees with f on 38,230
domain symbols. **There is no original-code decoder candidate for this column.**

Now answer each OOD point with the actual f value when that point is received.
This obeys the source order `zeta0; vector0; zeta1; vector1`; the first answer
does not depend on the second point. Let I be the verifier's affine interpolant,
and L=l_- z^-1+a+l_+ z its legal chord. Both chord endpoints are nonzero, and
L has no zeros on the base evaluation domain.

The polynomial z^512(f-I) vanishes at the two distinct nonzero OOD z values.
Dividing by zL gives a polynomial of degree at most 1022. Equivalently,

```
Q=(f-I)/L has Laurent support [-511,511], hence Q belongs to W.
```

For a nonzero gamma and occupied lane ell, the combined quotient is gamma^ell Q.
For every alpha its normalized four-slot fold is a line polynomial of degree
at most 255. The prover chooses exactly that final polynomial **after alpha**.
All 262,144 fibres agree. This counts all folded values, not just an all-zero
subevent, and it uses no challenge search, repeated nonce or PoW credit.

Why original reconstruction is still invalid is explicit:

```
l_+ Q[511] + l_- Q[-511] = 1
```

and gamma scaling makes the residual gamma^ell, still nonzero. The source-shaped
natural-tensor image constraints previously derived in `relation-link.md`
therefore cannot both hold. The quotient is low-degree but is **not in the
image of the selected original-code quotient map**.

This is materially different from the earlier `Q=z^511` reverse-membership
example: choosing Q first could make the reconstructed original word depend
on later OOD challenges. Here the malicious **base-field original word is fixed
first**, and the construction works for every legal OOD pair. Only the final
candidate uses its legitimate post-alpha adaptivity.

Scope safeguards:

- The universal quotient/fold derivation is mathematical, with exact coefficient
  tests below; it is not a fully kernel-checked QM31/source instance.
- H(T)=1 refers only to this algebraic chord/query experiment before requiring
  semantic/relation acceptance. Actual scheduler H(T) remains unknown.
- The literal V7 raw-word fold is different. This construction does not show
  perfect V7 query agreement or a V7 weakness.
- The narrow `Width29DecompositionFailure` requires an already selected original
  candidate. Here that original list is empty, so **H_width29(T)=1 is not claimed**.
  It obstructs the broader proposal to handle *all* unrecovered V8 branches
  through the quotient matching count alone.
- No complete earlier-semantic/terminal/pool-accepting proof or payment forgery
  has been constructed. A correct image/relation gate should reject this input.

## 3. A high-agreement control for the genuine width29 branch

Image constraints are not the entire repair. Retain the root-product construction
but choose J=252843 common zero fibres. There are T-J=9301 remaining fibres and
260428 distinct nonzero exceptional gammas, all below p. Set every non-common
fibre's 29 components to its monic degree-28 root-product coefficients.

The new, useful uniqueness fact is

```
agreement of any NONZERO original candidate
   <= 1024 + 4*(T-J) = 38228 < 38230.
```

Thus zero is the **unique** original close candidate for each component and
for the combined word. No convenient decoder ordering or `candidateMember`
premise selects it. It folds to the zero disclosed final, which is close because
the common fibres already suffice. At every exceptional gamma, the selected
combined zero candidate gains one extra matching fibre. D is one there, so
same-support decomposition fails. This is the actual mathematical width29
failure criterion in the original-code decoder model, determined before queries.

The disclosed zero quotient also satisfies the image constraints. For the chord
query model, all common-plus-one fibres pass for every alpha, giving the lower
bound

```
260428/(k-1) * choose(252844,22)/choose(262144,22)
  = approximately 2^-107.1559853192.
```

This subevent consumes about 0.7012% of a 2^-100 budget. It is **not an upper
bound**, not complete verifier acceptance, and not a counterexample to the
100-bit target. Additional folded cancellations can only increase its pointwise
acceptance probability. It does refute an attempt to assign the fixed-target
31/k-scale error directly to the genuine same-support outside event, even at
very high agreement. The old J=9557 and paired J=9556 subevents are retained with
neutral labels: this continuation does not establish their canonical selected
chain in every case.

## 4. Quantitative gap, without an invented tail envelope

The low bin M<=9557 contributes at most
`choose(9557,22)/choose(262144,22)`, or 105.1420996194 bits, for arbitrary adaptive
earlier prefixes with genuinely fresh conditional queries. This is the existing
query calculation, not the new recovery result.

As a generous diagnostic only, suppose the old gamma budget
336869026605739/(k-1) were applicable, and give the outside event the **entire**
2^-100 budget with no other terms. Query suppression alone would then require
a uniform cap M<=122072 (46.5668% of fibres). The next integer already fails
that diagnostic. The high-agreement control shows why a uniform cap is the wrong
shortcut; a rare high-agreement category must actually be bounded and charged.
The old budget is not granted applicability to V8 by this calculation.

No universal upper envelope for the image-valid, adaptively uncovered high-M
branches has been proved. Consequently there is still no composed 100-bit raw
or resource-bound FS theorem to report.

## 5. Executed evidence

- Supplied ZIP `aspis_v8_adaptive_query_review.zip`, SHA-256
  `dcc6ff045b570f3f74ae5394b1722e7ec82d1a8e21a5d1597e3bd4337ec66019`:
  all four files reviewed before execution; retained copy is byte-identical.
  Exact JSON reproduced: 3,586 matching-set cases, 4,096 weighted-prefix cases,
  freshness countermodel and 22-root shifted-batch instance. 0.16 s, 18,481,152 B
  RSS, zero swaps, exit 0.
- [adaptive_outside.rs](experiments/adaptive_outside.rs): optimized Rust using
  pinned production QM31/M31/circle arithmetic; four legal OOD pairs including
  equal-x/reversed endpoints, exact coefficientwise division/reconstruction,
  1,280 actual-domain fold checks and 32 nonzero image residuals. 0.94 s,
  2,441,216 B RSS, zero swaps, exit 0. No full prover or source verifier replay.
- [FullDegreeOutside.lean](experiments/FullDegreeOutside.lean): generic endpoint
  separation and <=1024 original-code agreement cap for every constrained target
  polynomial. Four declarations audited, no `sorry` or new axioms. 29.64 s,
  4,670,128,128 B RSS, zero swaps. Circle-index/encoder and quotient-existence
  packaging remain explicit mathematical/source bridges, not kernel-closed here.
- [adaptive_tail.py](experiments/adaptive_tail.py): exact high-agreement control,
  990 small monotonicity cases, two historical rational crosschecks and exact
  integer threshold search. 0.17 s, 20,512,768 B RSS, zero swaps, exit 0.

[Machine-readable results](adaptive-tail-results.json) and
[commands, hashes, failures/replacements and logs](adaptive-tail-evidence.json)
separate these evidence levels. Concurrent main semantic work was preserved;
its cache advanced to `00dccf39`, but the imported V5 module matches the research
parent byte-for-byte. No broad Lean replay, SBF build, remote job or deployment.

## 6. Next deciding experiment and recommendation

Keep QM31 q22 as research primary and full quintic q22 as the out-of-budget
fallback control. No size or CU finding changed. The full-quintic control retains
the unquotiented recovery architecture, so this particular chord-image gap is
not a reason to alter its recorded field-port requirements.

The next useful experiment is **joint image/relation accounting for the actual
post-gamma quotient candidates**, retaining all query/fold-outside branches.
Trace the full-degree fixture to a real checked discrepancy and establish its
fresh challenge boundary. If a new image term or challenge is required, it is
a verifier/design change, not a proof-only repair; recensus it and measure it.
Known-zero image claims may need no transmitted values, but they are not free
verification or free Fiat–Shamir operations.

Require this experiment to reject the T_512 fixture without assuming original
membership, and keep the image-valid high-J root construction as the next
coverage regression. Do not declare success after excluding the first fixture:
the remaining accepted adaptive high-agreement tail still needs a bound.
