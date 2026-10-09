# One common regular row for all retained higher factors

New leaf: [CommonRegularRow.lean](experiments/CommonRegularRow.lean).
Status: kernel checked with five standard-only audits. No compiler
was launched by this agent. The parent ran the serial capped NUC checks;
this agent verified their copied evidence locally. The earlier TailSum and LowSupport sources and their
[review](regular-low-support-composition-review.md) remain frozen.

## The strengthened source interface

The fixed pre-OOD polynomial remains
`SelectedSingularOODFamily.obstruction c1 c2`, a product over the actual
pre-OOD higher prime-factor multiset. Its already checked nonzero and
degree bound are unchanged. Keep the alternative that BOTH actual OOD
points are roots of this polynomial; do not assign that event a probability
without the applicable sampler law.

Outside that pair-root alternative, `common_row` chooses ONE row r where
the parent obstruction evaluates nonzero. For every retained factor F,
its factor obstruction is also nonzero there, so the existing
`SingularOODCoefficient.derivative_nonzero_of_obstruction` proves that
the actual derivative curve at this row is a nonzero polynomial in gamma.
This uses the actual OOD answer identity, not an assumed simple parent.

`derivativeProduct` is literally the multiset product of all those actual
derivative curves, including repeated factors. Its degree is bounded by

    sum_F (weight(F)-28) <= parentWeight-28 <= 117049.

The empty product is one, with zero degree and empty root set. All three
cases—empty family, repeated factors, and a nonsquarefree parent—are
included. The factor characteristic/separability work is reused through
the existing obstruction interface rather than assumed afresh.

The new `member_zero` proves the essential stronger implication:
if ANY retained factor's derivative vanishes at the selected row and
gamma, the derivative product vanishes there. Previously the exported
family theorem exposed only simultaneous singularity at both rows.
Thus `selected_common_row` returns r and a nonzero Z of degree at most
117049, with a root-set cardinality bound of 117049, and

    Z(gamma) != 0 implies every retained higher F is regular at row r.

The parent obstruction is fixed from C1/C2 before OOD. Row r and Z depend
on the completed OOD points and answers, but precede gamma and every
kappa/tau/alpha/query continuation. No candidate or final is an input.
Checked/image/circle-coordinate conditions are not needed for this larger
algebraic guard; they remain inputs to the downstream actual support tail.

Quantifier detail: `selected_common_row` takes the fixed finite Gamma domain
before returning r and Z. Use it with that domain fixed before the actual
gamma draw, not a future-dependent subset. If uniformity over subsequently
chosen finite subsets is needed, `common_row` already constructs r and Z
with NO Gamma argument; `product_root_count` then applies to each such
subset. Also, roots of the pre-OOD product at its two OOD points may come
from different factors. The pair-root alternative cannot be replaced by
one factor vanishing at both points.

## What this permits the low-event consumer to do

After retaining the pair-root and Z-root exceptions explicitly, every
actual retained higher-prefix witness uses the SAME fixed regular row.
The derivative product does not imply uniqueness across different factors;
it supplies the per-factor regularity needed by the already checked
source uniqueness/moment theorem.

The finite consumer can therefore sum per-factor low regular matching
moments using `SelectedRegularTailSum.tail_sum_bound`, without doubling
the incidence budget for the two rows. It must still use
`SelectedRegularLowSupport.shared_suffix` on the whole union once, not
sum per-factor suffix charges. The low witnesses retain their actual
post-alpha final and support range 9558 through 200807.

The integration source is owned separately by the transcript-refinement
agent as `SelectedRegularLayerCake.lean`. This leaf does not duplicate it
or claim its result. The precise finite formula and source seams are in
the frozen [low-support review](regular-low-support-composition-review.md).

## Symbolic arithmetic checks before integration

For l=9558, u=200807 and q=22 the exact increment is
`choose(m,22)-choose(m-1,22)=choose(m-1,21)`. Its nonnegativity requires no
probabilistic independence. The normalized denominator requires q<=262144.
Nonempty A gives epsilon=min(1,3/|A|) in [0,1], so multiplying the tail
bound by 1-epsilon preserves the inequality. The gamma denominator also
requires nonempty Gamma.

Both the baseline and all intermediate tails matter. A tiny exact check
with unnormalized q=2, support values 3 and 5, l=3 and u=5 gives

    choose(3,2)+choose(5,2) = 13
      = 2*choose(3,2)+choose(3,1)+choose(4,1).

Using only the upper-end tail gives 10, and omitting the baseline gives
7; both proposed shortcuts fail. The intended sum H(m) counts gamma/factor
incidences with multiplicity, not merely their gamma union, since distinct
factors can support different regular quotients at the same gamma.

Finally the conservative single alpha term needs its cardinal comparison:
`epsilon*H(9558)/|Gamma| <= epsilon` follows only after
`H(9558)<=6752623450<=|Gamma|`. It is false for arbitrary small Gamma with
multiple active factors. The selected nonzero-QM31 domain supplies the
large cardinality, but a theorem generalized to arbitrary finite Gamma
must keep this comparison or the full restricted correction term.

No numerical 100-bit conclusion, source transcript freshness, authentication
or payment/extractor result is asserted by this guard or these symbolic
arithmetic checks.

## Focused verification

| Attempt | Exit | Wall | Peak RSS (KiB) | Swaps | Result |
| --- | --- | --- | --- | --- | --- |
| [v1](experiments/common-regular-row-nuc-v1.log) | 1 | 3.32 s | 6840132 | 0 | First four audits passed; selected root-set specialization failed to transport the let-bound polynomial/filter instance. |
| [v2](experiments/common-regular-row-nuc-v2.log) | 1 | 3.22 s | 6841288 | 0 | Explicit filter equality left the selected-instance conversion failure. |
| [v3](experiments/common-regular-row-nuc-v3.log) | 0 | 3.25 s | 6879144 | 0 | Five audits standard-only; 963-entry preflight/postflight passed unchanged. |

V3 applies the same generic Mathlib root-subset theorem directly to the
opaque selected Z. This avoids comparing separately elaborated generic
and selected filter instances. The algebraic construction and first four
proofs were unchanged. No recursion, heartbeat or resource limit was raised,
and no concrete field/domain computation was added. All failed source
snapshots, manifests and logs remain retained; their `sorryAx` diagnostics
are not theorem credit. The final audit set is exactly `propext`,
`Classical.choice`, `Quot.sound` for all five theorems.

The inherited cache pin is `289d7356c78a4cd493fe61a54f9548f2a0c11298`, with
borrowed V7 source `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The parent ran over Tailscale:

    run_higher_y_nuc.sh TASK CommonRegularRow common-regular-row-nuc-v3

where TASK is `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`.
Lean 4.32.0 used `-j1 -M9500`; the cgroup caps were MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%. Source limits remained
depth 200 and 250000 heartbeats. No cold dependency or package replay ran.
The source/output and exact v3 triplet were independently hashed locally.

| Artifact | SHA-256 |
| --- | --- |
| Frozen source / v3 snapshot | `e618b11adb34811bc5e278784849c0cb74f9c4d021b2abab0ed7b17a4b35a436` |
| Olean | `42b73036bc0879cae8be1d7c12e980dd107a1f5954999c0165a2ca89b08e5955` |
| V3 manifest | `57a84e4324b26fd1feb22588cb823a7b98e71647235505b63e67ed3538a59fe3` |
| V3 log | `347ef849e906b27a31c8400abaa4f5b705366f616a290bcc275a747cd181f542` |
| Runner | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |
