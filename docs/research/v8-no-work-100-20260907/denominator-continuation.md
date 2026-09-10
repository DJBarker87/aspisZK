# All retained linear factors: selected-message classification

Parent: `2f6d82fef294410367aa1781fb924af7c38deab9`, existing branch
`research/v8-no-work-100-20260907`. All Lean jobs ran on the NUC as requested.
This continuation closes the supplied-rational-root restriction for the
**linear-Y** factor class and connects selected copy failures to the actual
early-C1 family. It does not close higher-Y recovery or payment extraction.

## Main result and exact scope

[SelectedLinearCover.exists_selected_classification](experiments/SelectedLinearCover.lean)
is kernel-checked. Fix arbitrary received C1/C2 at their legal boundaries.
From their unchanged interpolant parent P, before either OOD point, it
constructs one nonzero polynomial E and uses one mathematical family of at
most 111 tuples, each containing 29 actual 1,024-coordinate QM31 messages.
The family's definition depends on P alone. Gamma's sampled universe is
also fixed before the actual draw.

For the SAME candidate from `SelectedIdentityCover.Root`, selected even
after alpha, at least one of these holds:

1. Both actual OOD parameters are roots of E, with degree at most
   **26,854,534,485**.
2. The actual gamma is in a fixed sparse set of at most **3,108** elements.
3. The actual candidate is rooted in a retained prime factor of Y-degree
   at least two.
4. Its literal reconstructed message `(atGamma d gamma).original Q` equals
   the gamma-power batch of a tuple in the fixed family.

This is a covering union; the theorem does not claim disjointness. Priority
tests can make a classifier disjoint without dropping any branch. No
supplied rational-root polynomial, monicity, successful provider or
retrospectively fixed candidate is assumed. Encoder injectivity gives
actual message equality, not merely equal evaluations at the queried points.

The input is the existing selected-model `Root`, not bare verifier
acceptance. Its same-Q source-shaped construction and the preceding causal
image/ordinary relation reduction remain the route into this theorem.
Their hypotheses, missing-prefix mass and authentication/replay boundaries
are not deleted. The degree-two helper curve, degree-28 gamma claim error,
shifted ordinary rows, carried image weights, general degree-q query batch
and adaptive final timing are inherited unchanged.

## Why the remaining denominator classes are now covered

Write a fixed prime linear factor as `A(X,Z)Y+B(X,Z)`.

| Factor class | Newly proved treatment |
| --- | --- |
| A has positive gamma degree | Primitivity derives nonzero resultant; `lc_Z(A)*Res_Z(A,B)` catches every polynomial OOD identity, including degree drops |
| A is gamma-constant, B has gamma degree above 28 | One fixed nonzero high coefficient of B must vanish at each OOD point, even if A also vanishes there |
| A is gamma-constant, B has gamma degree at most 28 | Construct `R=-B/A` in `K(X)[Z]` and prove its degree and exact equation; reuse checked interpolation/code-image descent |

The last row is a mathematical fraction field, not a changed protocol field.
It includes X-dependent denominators and consumes the earlier rational-helper
control honestly. With more than 28 original-code specializations, the
constructed curve has actual source-message coefficients and covers every
later polynomial root. Otherwise only the actual hit on the sparse set is
charged. Unioning these sparse sets over the fixed factor family costs
`111*28=3108`, **not 111 copies of the q22 query tail**.

The OOD product uses the sum of individual factor X-degrees, not a parent
degree charged independently to each factor. Its degree cap is
`(2*117077+1)*114687`. See [the denominator proof map](linear-denominator-review.md).

The regression `F=(XZ+1)Y+1` is now proved prime and primitive in Lean.
Its original resultant is 1, but at X=0 the answer −1 is an exact OOD
identity. Thus a resultant-only proof would be false. The leading-coefficient
factor supplies the necessary root; it is not an optional numerical loss.

## Early-C1 copy connection

[EarlyC1CopyCollision](experiments/EarlyC1CopyCollision.lean) consumes the
existing unfiltered family of at most 100 C1 tuples fixed **before lambda**.
It proves the selected first-sixteen-column copy-table projection and carries
the literal late 26+3 projection's own support into that family.

For every adaptively chosen in-family table/helper satisfying the actual
selected local, total-helper, inactive-helper and all-slot non-pole
premises, failed weighted aliases lie in the sequential collision union:

`217600*|Chi| + 27100*|Lambda|` challenge pairs.

The fine bound retains the actual active-link count n≤136. Lambda error
polynomials are fixed from each early table; chi Wronskians are fixed after
lambda but before chi. No post-C2 table is moved backward in the transcript.
See [the covered-event/source map](early-c1-copy-collision-review.md).

The **new 111-member, 29-message family is not this early 100-member family**.
It depends on adaptive C2 and has no proved component own-support floor.
Its first 26 columns cannot be inserted into the copy result until the
own-support/descent bridge is established. The zero placeholder in the raw
family definition also does not make every enumerated member recoverable;
the selected branch supplies its particular all-root cover.

## Ledger and accepted-extraction accounting

[denominator-ledger.json](denominator-ledger.json) contains exact rationals.
The following are separate stated ideal-law interpretations, not a composed
security certificate:

| Event/model | Display bits | Status |
| --- | ---: | --- |
| Both E roots, uniform distinct parameters in K minus CM31 | 178.71110667 | Finite root count plus exact arithmetic; bounded source sampler/FS lift not instantiated |
| Same E, only one uniform parameter | 89.35555334 | Insufficient on its own; do not lose the second OOD boundary |
| Actual sparse gamma hit across fixed factors | 112.39822921 | Cardinality proved; needs fresh uniform nonzero gamma law |
| Covered early-C1 copy collision pair | 106.09934542 | Cardinality and source-conditioned coverage proved; actual acceptance/prefix-law composition open |

The previous local reduction ceiling is unchanged (about 104.366 bits).
The new denominator event subsumes the previous monic-only event; it is not
added a second time. No relation-repair, content, derivative or historical
396430 term is duplicated. The copy model is not blindly added to an
unrelated reduction subtotal. Global allowance and global extraction bound
remain null in the machine ledger.

For the actual target `A AND NOT X`, X must still be a resource-bounded
extractor returning a checked payment witness. The following contributions
remain visible, not assigned invented probabilities:

| Execution/class | Current treatment |
| --- | --- |
| Upstream source/causal reduction failures | Keep the existing exact events and fixing prefixes |
| Selected Root with excluded linear factor | New E-root or sparse-gamma events |
| Selected Root with retained higher-Y factor | Explicit unbounded residual |
| Represented tuple without enough component own support | Explicit unbounded residual; not early-C1 membership |
| Supported tuple with copy premises | New covered copy collision/success alternative |
| Supported/correct-copy tuple without checked witness | Semantic, descent, decoder and resource obligations remain |
| Authentication/source mismatch; replay/fuel/abort/missing/challenge mismatch/provider none | Must be coupled to X and accounted separately |

Represented or out-of-radius executions that yield a valid witness are
successes, not part of failure. Neither a mathematical family nor failed
decoding by one procedure certifies success or impossibility of another.

## Evidence, costs and reproducibility

Ten focused new leaves passed on the pinned NUC cache; 56 named audits
report only `propext`, `Classical.choice`, `Quot.sound`. No retained claimed
result uses `sorry` or new axioms. The complete run/source/olean provenance,
exit, wall time, peak RSS and swap census is in
[denominator-build-evidence.md](denominator-build-evidence.md).

The selected endpoint needed P-abstract handlers before its concrete QM31
instantiation: five diagnostic attempts hit the recursion cap while
normalizing the nested source parent/membership interface. The final check
passed in 3.29 seconds at 6,868,460 KiB RSS, zero swaps, with the original
recursion/heartbeat/memory limits. Every failed source/log is retained and
distinguished from green evidence. No concrete field enumeration, package
replay, Aeneas or SBF build was run.

Reproduction from the verified NUC overlay (do not rerun unchanged greens
merely for activity):

```
bash /home/dombarker/project-offloads/aspis-denominator.QNcd5G/run_denominator_nuc.sh \
  /home/dombarker/project-offloads/aspis-denominator.QNcd5G TARGET fresh-tag
python3 docs/research/v8-no-work-100-20260907/experiments/denominator_ledger.py --check-recorded
python3 docs/research/v8-no-work-100-20260907/experiments/audit_denominator_evidence.py --check-recorded
```

All compiler runs are serial, MemoryHigh8GiB/Max10GiB/SwapMax0, CPU200%,
`lean -j1 -M9500`. The laptop only edits and checks metadata/small arithmetic.
The isolated overlay preserves frozen imported bytes despite concurrent main
work. No production files or defaults are changed. Main advanced independently
during this turn and its uncommitted V7 work was left untouched.

The body stays `697*16+52+24+22*621+2*296*26 = 40,282` bytes. This turn adds
zero verifier operations or public messages. It measures no CU, prover time,
SBF stack, or replay-extraction runtime. Full-view ZK and resource-bounded FS
remain independent obligations; grinding security credit is zero.

## Decision and one next experiment

Continue q22 research: this removes a real restriction from the retained
linear-factor reduction without protocol changes. It is not a production
readiness verdict. The original/paired root products, high-J own-support
case, T512/image kernel, shifted-row/query collisions and radius9302 control
remain intact; none is erased by the new family.

The next decisive leaf should bound **represented tuples with insufficient
own support jointly with the actual queries**. First prove the exact
source-shaped identity eliminating adaptive Q from the good-covered query
residual: it becomes the fold of
`(received_gamma - encode(batch_gamma(tuple)))/L`. The tuple was fixed
before gamma; the candidate need not have been.

Then test the following proposed split before retaining a theorem: fewer
than 38,228 own symbols gives at most 9,556 common full fibres. A covered
candidate nevertheless has at least 38,230 batched original-symbol matches,
forcing an outside-support degree-28 residual root. Charge that gamma event
on all-common schedules; on other schedules reuse the existing fixed-target
joint gamma/alpha bound, with literal chord/slot transport and pole rejection.
Union only the charged algebraic terms over the 111-member family, not the
bare query tail. Rho/later repairs must be charged once. This is a next
proof target, not an established new upper bound. Higher-Y factors remain
a separate explicit obligation even if that bridge succeeds.
