# Exact ordered alpha/query matching moment

Status: **kernel checked** on the capped NUC runner. New source:
[RegularQueryMoment.lean](experiments/RegularQueryMoment.lean). It imports the
existing `SelectedRegularQueryBridge`; all eight printed theorem audits use
only `propext`, `Classical.choice`, and `Quot.sound`. All numerical operations
remain symbolic finite sums/cardinalities; no QM31 or query-domain enumeration
is performed.

## Hypothesis checks and falsifiers

An unrestricted adaptive-final claim is false. For one queried fibre and
q=1, let A be a five-element field and let the received slots differ from a
fixed Q. After seeing each alpha, choose a constant final that matches the
received folded value at the sole query point. Every alpha then matches,
while the proposed fixed-Q formula would have b=0 and bound3/5. The missing
hypothesis is identification with folds of the SAME Q across the counted
alphas. This toy falsifies an unrestricted final theorem, not the checked
selected regular branch, whose source uniqueness proves that identification.

Even for fixed Q, a non-full fibre cannot be charged zero: invert the radix
transform of a cubic having three distinct roots to choose its nonzero
slot residual. For a single query its matching-alpha fraction is exactly
3/|A|. When |A|<=3 the generic bound must be capped at1 to be a sharp
probability upper bound; the draft does not impose |A|>=3.

The ordered product average is also essential. A query mechanism that sees
alpha and deliberately chooses a matching location does not have the
uniform ordered-schedule mass used here. The theorem is a finite counting
identity and inequality, not a discharge of that source sampler law.

## Exact statement and fixing

Fix gamma, factor F, regular row r and one qualified actual quotient Q.
The received quotient word is fixed. Let C be the actual field-domain
fibres on which all four encoded Q slots equal that received word, and set

    b = choose(|C|,q) / choose(|domain|,q),
    epsilon = min(1, 3/|A|).

For nonempty A and q<=262144, `fixed_fold_moment` proves

    avg_alpha matchingRatio(fold_alpha(Q), receivedFold_alpha)
      <= b + (1-b)*epsilon.

No polynomiality of the received word, full-support assumption, or chord
nonpole resampling is needed. C is the literal quotient support on the same
query domain, not the width29 own-support set or a different symbol set.
The existing point/index inverse transports the actual indexed fibres.

`adaptive_regular_moment` retains the actual strategy final and actual
regular-event indicator inside the alpha average. It uses
`SelectedRegularQueryBridge.regular_matching_moment_bound`; this invokes
regular uniqueness only when the actual branch qualifies. Kappa and tau
are fixed before alpha; the final still depends on alpha. Q can depend on
gamma, and the theorem never declares it a polynomial curve in gamma.

The direct `regular_suffix_bound` consumer adds q/|G|+18/|A| once, using the
already checked compact-suffix reduction. It does not add a first-response
6/|A| charge or a per-factor repair multiplier. Crucially, no count or
probability of regular gammas is multiplied into this joint moment.

## Reused exact counting, not independent labels

`OrderedQueryGame.Schedule domain q` is an embedding Fin q into the domain.
`matching_card` counts matching ordered embeddings by descending factorials,
and `ordered_matching_ratio` cancels the q! factor exactly to the choose
ratio. This preserves first-occurrence order; no continuation is assumed
permutation-invariant.

The new generic proof first writes the choose ratio as the exact uniform
ordered-schedule indicator mean. Finite sum commutation exchanges the two
explicit means. Full-support schedules cost at most1; every other schedule
has at most three matching alphas by the source four-slot fold theorem.
Their masses partition exactly, giving b+(1-b)*epsilon rather than b+epsilon.
The generic matrix theorem allows any per-schedule degree cap d and proves
the analogous min(1,d/|A|) bound. It does not assume the per-alpha matching
sets are independent or equal.

Boundary cases are explicit: q=0 has its unique empty schedule and b=1;
an empty full-support set with q>0 has b=0; q exceeding the domain is excluded
from the normalized experiment. A is required nonempty. Multiplying by an
unrelated gamma marginal, replacing the actual raw word, or dropping the
regular indicator would be a different and generally false theorem.

Actual transcript freshness, the ordered query sampler coupling, aggregate
higher-factor acceptance, extraction, and payment remain outside this leaf.

## Focused verification

Five focused attempts were retained. V1 exposed three rewrites whose inferred
predicate decision procedures differed from their source expressions, plus a
missing namespace qualification. V2 and v3 confirmed that proof-irrelevance
does not make distinct `Decidable` programs definitionally equal. V4 added
explicit predicate-decision interfaces and left only selected predicates
without instances. V5 supplied one selected classical decision boundary and
passed.

The final command was:

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  RegularQueryMoment regular-query-moment-nuc-v5
```

It exited 0 in 3.62 seconds, with peak RSS 6,885,348 KiB and zero swaps.
The cgroup used MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPUQuota 200%, Lean 4.32.0, `-j1 -M9500`; both 947-entry provenance checks
passed unchanged. One style-only `unnecessarySeqFocus` warning remains at the
final algebraic rearrangement. It does not affect the theorem or axiom audit;
the checked source was retained exactly instead of mutating a frozen green
artifact merely to remove the warning.

| Artifact | SHA-256 |
| --- | --- |
| Source / v5 snapshot | `7db76b9373e824caa4ba5ebe5c6744b0e57e6fad71663514caee6c7be793125e` |
| Olean | `00feb4fd07a78f741cc0b90dcdb99dc014d4ccacc2021fb4d581f5912ec389fd` |
| V5 manifest | `401bcfea758440f0101424b066d59e555da343eaf7e41eda209ffabde4f731d8` |
| V5 log | `2fc31d1e35ae2d8b0ac776a5843374812cb32a962d6a3a49dfa47c0186524f58` |

This is an ideal finite-game theorem. It neither proves the Fiat--Shamir law
nor turns the still-uncovered high-support extraction region into a small
event.
