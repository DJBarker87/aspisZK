# Regular low-support composition: exact source seams

Source parent: `69f4cee939cfa3fe300f77c6508ca1b07a5567fc`.
New sources: [SelectedRegularTailSum.lean](experiments/SelectedRegularTailSum.lean)
and [SelectedRegularLowSupport.lean](experiments/SelectedRegularLowSupport.lean).
Status: both focused leaves are kernel checked, with thirteen standard-only
audits in total. This is not yet a completed layer-cake or global probability
theorem. Green sources are frozen. The parent coordinated and ran the NUC
checks; no compiler was launched by this agent.

## Additive factor budget and actual tail counts

`selected_budget_sum` uses the actual pre-OOD higher-factor MULTISET. For
each occurrence, its weight W and checked regular-branch budget B satisfy

    B + 57288 = 2047*W.

Every included factor has Y-degree at least three, so W>=28. The parent
budget gives sum W<=117077. For a nonempty multiset, summing the identity
and removing at least one 57288 gives sum B<=239599331. The empty case is
zero. Multiplicity is preserved; no disjointness or unique factor is used.

For one row r fixed after OOD and before gamma, `tailSum M` sums the actual
`SelectedHigherYRegularTail.supportGammas ... M` cardinality over all
retained higher factors. It does not merely take their union. The source
theorem `tail_sum_bound` states

    (M-1024)*tailSum M <= 1048576*239599331.

It directly adds `support_tail_count`, whose candidate and support inputs
are already derived from actual Qualified quotients. At M=38230,
`minimum_tail_sum` gives the denominator 37206. This stronger SUM bound is
the correct input for both query-support integration and alpha correction.
It does not cost an extra factor-cardinality multiplier.

## Same-Q low event through 200807 fibres

`lowRegularPrefix` is the intersection of the checked `LowPrefix` and
the actual fixed-factor `fixedRegularPrefix`. It does not discard any
post-alpha final dependence. Assuming that F belongs to the actual retained
higher family, `low_regular_witness` derives an actual Q representing that
final and its exact support range

    9558 <= fibreCount(e.raw gamma,Q) <= 200807.

The upper bound uses `low_witness_bad` for that SAME witness. The lower
bound is literal quotient-family membership, not a supplied decoder event.
`full_bad_card` connects the complete indexed support to the source bad-fibre
set without concrete enumeration.

`fibre_to_original_support` reuses the sharp two-SYMBOL pole loss to prove

    4*fibreCount <= originalSupport.card + 2.

Thus `regular_fibre_tail_mem` transports any actual quotient support at
least m into the exact existing `supportGammas (4*m-2)` event. In particular
for m>=9558 its incidence denominator is 4*m-1026. No two-whole-fibre
deletion, nonpole resampling, raw-word polynomiality or fixed pre-gamma
candidate is introduced.

`full_query_mass` proves the other required coordinate transport:

    fullQueryMass received Q q
      = choose(fibreCount received Q,q)/choose(262144,q).

The field-domain full-support set is the image of the SAME indexed support
under the existing point/index bijection. This is not an independently
supplied query domain or matching statistic.

`low_regular_moment` restricts the already checked adaptive regular moment
to this actual low event. For each fixed F/gamma and qualifying Q it gives
`b+(1-b)*epsilon`, with epsilon=min(1,3/|A|). It contains no suffix repair
term, so these restricted moments can be summed before charging repairs.
The existing regular uniqueness theorem identifies all same-F witnesses at
that gamma; it does not assert uniqueness across factors.

`regularLowUnion` retains all actual factors and the same shared strategy.
`shared_suffix` applies `causal_supported_bound` to that UNION exactly once,
leaving its finite compatible matching moment and adding only
q/|G|+18/|A|. It does not sum per-factor repair charges. Fixed early C1 is
unchanged; these low-event adapters happen to hold even when the optional
early object is absent. Its population is needed by the separate high
count, not silently inferred here.

## The exact finite integration still required

For each factor F let S_F be the gammas at which an actual low regular
prefix exists. Regular uniqueness supplies one Q_F,gamma from the fixed
received/OOD/gamma data and its support m_F,gamma. Every actual later
witness on that fixed factor has that Q; the proof need not freeze a
prover's final before alpha. Define

    H(m) = sum_F card{gamma in S_F : m <= m_F,gamma}.

The source adapters above give the intended bound

    H(m) <= floor(251238108102656/(4*m-1026)),  m>=9558.

For l=9558, u=200807 and beta(m)=choose(m,q)/choose(262144,q), the remaining
finite integration must establish the literal identity

    sum_F sum_gamma_in_S_F beta(m_F,gamma)
      = beta(l)*H(l) + sum_{m=l+1..u} (beta(m)-beta(m-1))*H(m).

Then the summed matching-moment contribution is bounded by

    (1-epsilon)*[the integrated beta numerator]/|Gamma|
      + epsilon*H(l)/|Gamma|.

For q=22 the increment is choose(m-1,21)/choose(262144,22). This is an
integration of the actual support distribution, NOT a product of a gamma
marginal and an unrelated maximum matching mass. The generic layer-cake
identity has not been reproved or imported as a placeholder premise in
these leaves; the directly instantiated finite consumer is still needed.

The alpha term is also legitimately additive. The minimum tail yields
H(l)<=6752623450. Once the selected cardinal comparison
6752623450<=|Gamma| is instantiated, its contribution is at most epsilon,
and hence at most 3/|A|. That is the justification intended by the saved
arithmetic screen's conservative single 3/k term. A standalone 3/k bound
for an arbitrary union of fixed-factor events would be unjustified.

## Common-row singular split remains an explicit adapter

The tail theorem is for ONE fixed row r. Summing both rows' regular events
would in general double the budget. The checked
`SingularOODFamily.retained_derivative_cover` internally chooses a common
row where the fixed parent obstruction does not vanish, and constructs
the product of all retained factors' derivative curves at that row. Its
current exported conclusion, however, only says that simultaneous
singularity at both rows forces a product root.

The needed strengthened interface must expose the same constructed row
and product Z, with Z nonzero, degree<=117049, and

    for every retained higher F and gamma,
      Z(gamma) != 0 -> derivativeCurve(F, selectedRow)(gamma) != 0.

That is an enlargement of the exceptional gamma event to selected-row
singularity, not a claim that the old both-row singular event already
equals it. The pair-root alternative for the fixed pre-OOD obstruction
remains explicit. This extension appears available from the existing
product proof, but is not yet an exported theorem in these new leaves.
No two-OOD sampler probability is assumed.

Distinct factors really can have different regular candidates. For
example set H=X(X-1), u_i=iH, and over a small field of characteristic
greater than three consider

    F_i = Y^3+Y-u_i^3-u_i-(Z-b)H,  i=1,2.

Each is primitive and irreducible as a polynomial linear in Z. Both OOD
coordinates zero and one have answer polynomial zero and derivative one.
At gamma=b they admit distinct polynomial roots u_1 and u_2. Hence
per-factor regularity is not global candidate uniqueness. This is a
source-hypothesis falsifier, not a selected-interpolant or acceptance
fixture; it explains why the summed tail and alpha accounting matter.

The common-row export, instantiated finite support integration and ideal
sampler/source coupling remain separate obligations. These leaves neither
prove the saved numerical screen nor a global 100-bit statement.

## Focused checks and frozen evidence

| Target / attempt | Exit | Wall | Peak RSS (KiB) | Swaps | Result |
| --- | --- | --- | --- | --- | --- |
| [TailSum v1](experiments/selected-regular-tail-sum-nuc-v1.log) | 1 | 3.65 s | 6846132 | 0 | Generic proofs passed; explicit multiset card-zero implication was needed. |
| [TailSum v2](experiments/selected-regular-tail-sum-nuc-v2.log) | 0 | 3.83 s | 6878744 | 0 | Six standard-only audits, 959-entry provenance unchanged. |
| [LowSupport v1](experiments/selected-regular-low-support-nuc-v1.log) | 1 | 16.27 s | 6842868 | 0 | Missing storedPoint namespace caused elaboration timeouts; arithmetic also needed the literal e.raw alias identified. |
| [LowSupport v2](experiments/selected-regular-low-support-nuc-v2.log) | 1 | 3.54 s | 6845852 | 0 | Only the final fibreCount definition remained to close after exact set/card rewrites. |
| [LowSupport v3](experiments/selected-regular-low-support-nuc-v3.log) | 0 | 3.84 s | 6881188 | 0 | Seven standard-only audits, 961-entry provenance unchanged. |

All failures retain their exact source snapshots, logs and per-run manifests;
their cascading `sorryAx` output is never theorem credit. The successful
audits contain only subsets of `propext`, `Classical.choice`, `Quot.sound`.
Copied source snapshots, logs, manifests and both green outputs were hashed
locally and matched the recorded remote values.

Inherited runner/cache pin: `289d7356c78a4cd493fe61a54f9548f2a0c11298`;
borrowed V7 source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Both targets used Tailscale transport and the existing
`/home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh`,
with the task directory, target and fresh attempt tag as its arguments.
Lean 4.32.0 ran `-j1 -M9500` under MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0, CPUQuota 200%; source depth stayed 200 and heartbeats
250000. No limits were raised, no field/domain enumeration was added,
and no cold dependency or package replay occurred.

| Green artifact | SHA-256 |
| --- | --- |
| TailSum source / v2 snapshot | `e3b23c4194780b391fc13196113d658ee989ab6aed1f3a6e20e6fec6a63909ab` |
| TailSum olean | `7844a7c3f724da47c2f12a24420fbd287bf839043aeb8818e061947657bc642f` |
| TailSum v2 manifest | `6ceb049b4ada8386affbd6d84622e009dddc6a09e50187ce41ff7d482ae8efb1` |
| TailSum v2 log | `30ef273e15a4825ed3b7b28cfb1e1f3ce9bc6d7c00ba5e43d4b9b4fcadd48b50` |
| LowSupport source / v3 snapshot | `4fdefe2e4a7f6f44e66461871b3c8dbcc4b8377abd0bd50729fc154202faf70b` |
| LowSupport olean | `178528b724f6e34c559a672e7dedb67544300139fc6958a7ddd89ce316802ce2` |
| LowSupport v3 manifest | `224df4dd8970f30196ad84bdf7745a839ee0a85614347b80663eb4ceedd13b1a` |
| LowSupport v3 log | `355d30a0958b598193bb8a2f4f077a7eb8fdfc07ef3bd2b13616757b0d118d4c` |
| Runner | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |
