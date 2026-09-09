# Partial-fold recovery and the positive-residual degree gate

Continuation of `d5507a8f247bbed7cd35591c240d8d7a40af67a0`.
No Rust, wire, transcript, mask inventory, verifier default or production
change is made in this follow-on. The earlier opt-in profile and its measured
host evidence remain exactly as committed. The maximum body stays40,282 bytes.

## New partial-agreement information

Fix the actual received virtual quotient before alpha0. For four distinct
folding challenges, allow four arbitrarily selected final coefficient
vectors. If each evaluated final matches the actual normalized fold outside
at most `B` fibres, interpolate the four final-code words in alpha and apply
the invertible local four-slot map. This constructs a **global full-code
quotient** agreeing with all received slots outside the union of those four
bad supports, hence on all but at most `4B` complete fibres.

This recovers a codeword from the four finals; it does not assume an anchor,
received polynomiality, membership in a supplied family or provider success.
The reconstructed word need not be image-valid or recover all29 components.
It can depend on all four finals; it is not silently fixed before tau/gamma.

The contrapositive bounds a genuine high-agreement tail: if the fixed
received quotient is farther than `4B` fibres from **every** full-code
quotient, at most three alpha values permit any final within `B` errors.
This is stronger than only the globally exact (`B=0`) statement, but it is
not sufficient for the global q22 argument.

Given the four final coefficient vectors, an explicit interpolation recipe
is to take each coefficient lane as a sum of those vectors weighted by the
corresponding cubic Lagrange-basis coefficient. The current proof's
restricted-code membership construction is mathematical existence. It is
not an implemented resource-bounded rewind extractor, and it does not claim
access to four appropriately fixed-prefix accepted finals.

## Why the generic factor four cannot simply be improved

The new exact F31 control uses seven complete, disjoint circle fibres with
nonzero coordinates and distinct final points. For fixed distinct
`a1,a2,a3,a4`, assign one fibre to each cubic

```
r_i(X) = product_{j != i}(X-a_j),
```

and assign the other three the zero decoded coefficient vector. Convert
these coefficient vectors to actual four-slot received values before alpha.
At `alpha=a_i`, all folds but the ith equal zero: a constant final is one
fibre away. Yet any full lift of the constant final code has the same
four decoded coefficients on every fibre. The zero tuple appears three
times, each nonzero tuple once, so the nearest full-code distance is exactly
four. The four error supports are disjoint and their common good support
has three fibres. Replicating the groups on a larger eligible circle domain
with7B distinct fibres gives the same `4B` phenomenon; F31 itself has only
the seven non-axis fibres used here.
It also shows why the far-word premise needs strict `>4B`: at equality this
example has four close-fold challenges, contradicting a proposed cap of three.

The executable checks verify the local inverse on basis vectors and all
31alpha ×31constant-final pairs. They exhaust the **adaptive constant-final
selection** for this one fixed received word. For two fresh distinct queries,
the optimal pointwise passing probability in that toy model is exactly
`47/217`. No compact relation responses, image constraints, pre-OOD payment
commitments or valid-witness failure are asserted. This falsifies a generic
smaller-factor support shortcut, **not** a stronger theorem using the selected
code plus image/ordinary-row constraints.

In fact the fixed zero final is optimal for every alpha, so adaptivity is not
needed for this obstruction. Away from the four nodes, the nonzero values
are `S(alpha)/(alpha-a_i)` and are pairwise distinct. Zero matches three
fibres there and six at a node. For q2 the exact expression is
`(4/k)*15/21+(1-4/k)*3/21=(k+16)/(7*k)` for this construction over an eligible
field; it is47/217 at k31. This is still only the stated toy pointwise game.

## Exact quantitative reach, without a security headline

For the far-word premise above, fresh uniform alpha and a final fixed before
distinct queries uniform conditional on the complete post-final prefix give
the conditional pointwise bound

```
3/k + choose(T-B-1,q)/choose(T,q).
```

Outside the at-most-three exceptional alphas, every final has more than `B`
bad positions. This upper-bounds pointwise acceptance; it does not account
for scalar-only acceptance, later relation repair or source/replay coupling.

For the far premise even to be nonempty, `4B<T` is necessary. Giving this
route the most optimistic allowed value at `T=262144`, `B=65535`, `q=22`
leaves a matching cap of196608. The exact rational screen is only
**9.1312487764 bits**, including `3/k`. Smaller `B` makes this screen weaker.
Additional restrictions on the selected code can only make the displayed
far-premise range less optimistic. Thus generic four-support interpolation
plus query suppression cannot by itself certify the requested100 bits.
This is a limit of that bound, not a lower bound on the protocol's true error.

The exact integers, rational expression and toy evidence are in
[the reproducible control](experiments/partial-fold-control-output.json).
No Monte Carlo or work-normalized calculation is used.

## Where the accepted failure mass goes

The target remains `Pr[A AND NOT X]` for a specified checked-witness
extractor. The new far/close classifier refines only the faithful ideal
non-polynomial branch of the previous event table:

| Prefix / later event | New information | Still needed |
|---|---|---|
| Received word farther than4B from the full quotient code; final has at mostB errors | At most three eligible alpha values | Actual source/oracle and fresh-law coupling |
| Same far prefix; final has more thanB errors | Matching capT-B-1 | Useful image/relation-constrained bound, not the weak query-only screen |
| Some full-code quotient is within4B | Construction applies if four appropriate finals are supplied; their access/existence is not implied by this row | Image validity, component recovery, early C1 semantics and witness extraction |
| Replay/provider/fuel/authentication/source failures | No branch removed | Explicit total extractor accounting and bounds |

Existing exact-invalid-image and near bad-binding results remain separately
scoped. None is added twice, nor is the whole near class assigned its
bad-binding ceiling. Successful out-of-radius extraction still contributes
zero to `A AND NOT X`. Root-product, T512, image-kernel, row/query-cancellation
and radius-boundary regressions are preserved without replaying unchanged
heavy suites.

## Degree obligation closed for the added polynomial

The new positive-transfer residual uses the actual polynomial successor
point, not an MLE of a pre-permuted table. Along one sumcheck coordinate,
the source carry is a strict suffix product of distinct coordinate factors.
Each successor coordinate is therefore affine in the varying coordinate.
Composing an arbitrary10-coordinate multilinear table with that point has
degree at most10. The two ordinary table evaluations add at most1 each;
the row1014 selector and equality selector add at most1 each. The resulting
positive-terminal addition has degree at most14, including its fixed
extension-field packing scalar. Finite sums over the remaining Boolean
assignments preserve the bound. This fits the existing degree27 grammar
provided its existing part has the already-required degree27 bound.

The focused theorem/evidence reports distinguish this source-shaped
polynomial result from full Rust lowering, the acceptance-to-residual theorem,
and a privacy simulator. Removing one mask generator still needs the actual
q22 full-view analysis. No new CU result is inferred from the degree proof.

## Checked targets and reproduction

The generic support construction and its selected natural1024/log20,
natural256/log18 specialization are kernel-checked; see
[partial-fold proof and provenance](partial-fold-review.md).
The added degree bound and exact optimized last-coordinate successor identity
are kernel-checked; see [degree proof and source limits](positive-residual-degree-review.md).
All three leaves use standard axioms only, with no retained `sorry` or new
axioms. Focused builds reused cached dependencies, ran serially under the
7-GiB aggregate guard, and recorded zero swap. Local failed syntax/type checks
are retained as diagnostics, not counted as proved results.

[Current-source evidence](partial-degree-evidence.json) records source/olean
hashes, exit status, wall time, peak RSS, axiom audits and the exact conditional
arithmetic. It also keeps unbounded global events visibly null.

```
python3 docs/research/v8-no-work-100-20260907/experiments/audit_partial_degree.py --check-recorded
python3 docs/research/v8-no-work-100-20260907/experiments/partial_fold_control.py --check-recorded
```

The independent read-only review checked the slot signs, strict4B boundary,
query off-by-one, final-selection timing and fixed-zero optimality. It did
not run a new Lean or complete verifier replay. Source/report whitespace is
checked separately from unchanged raw failed-compiler diagnostics.

## Decision

Retain the constructive partial-support reduction and its sharpness control.
Do **not** tune its weak query-only screen into a global security ledger.
The next decisive mathematical step must use image/ordinary-row information
to constrain the reconstructed partial anchors or recover a checked C1
witness; generic code geometry alone has now hit an explicit limit.
Global recovery, source/FS composition and full-view ZK remain open, with
no numeric remaining global allowance asserted.

**Single next experiment: a pre-tau geometric-anchor dichotomy.** Define good
alpha values from the fixed received quotient alone by existence of a
B-close final, without a transcript/provider filter. If there are fewer
than four, charge at most3/k only on executions selecting a B-close final.
Otherwise select four from that geometry before tau and use the proved
reduction to obtain Q within4B. Any other B-close final agrees with
`Fold_alpha(Q)` on at leastT-5B points. Under `T-5B>255`, the selected final
polynomial overlap theorem should force equality, even if that final was
chosen after tau/alpha. This prospective step must be instantiated and
checked; it is not included among this continuation's completed theorems.

Use `B = 2,325` as a focused control: `4B = 9,300` stays inside the prior
9,301 near-anchor radius, while `T-5B = 250,519` exceeds255. Then test whether the existing carried
image/shifted-row game can use this genuinely pre-tau Q to bound accepted
wrong-image/row cases with represented finals. Do not infer image validity
deterministically from four accepted alphas: four roots cannot force a
degree-six relation discrepancy to be zero. Keep both the sparse-good branch
and finals farther thanB explicit. A geometric choice over all parameters
is still not a bounded replay extractor. Stop this route if it assumes
post-tau membership or silently drops those remaining executions.
