# Aspis V8: the next adaptive query gate

Reviewed revision: `1803896acf5d8c4ebe769b3927010031faf40e0e`.
Research only. Keep the accepted 40,282-byte allowance and existing production
protocol unchanged. Respect AGENTS.md and concurrent work.

## What is now settled, and what is not

`experiments/FixedTargetQuerySupport.lean` proves the generic fixed-target
four-slot algebra and finite-product query count. Its target residuals and
chord data are fixed before gamma/alpha. The recorded Lean replay audited
17 declarations with ordinary foundation axioms and no sorry/new axioms.
This review inspected source and evidence; it did not replay Lean.

Use general Tag-73 shifted cancellation **q/(|K|-1)** unless the prior
relation discrepancy is proved zero. The generic polynomial is

    D(rho) = prior - rho * sum_i residual[i] * rho^i.

This can actually have q nonzero roots: take D(X)=product_{j=1}^q(X-j),
prior=D(0), residual[i]=-coeff(D,i+1), in characteristic exceeding q.
Thus q-1 is not a generic improvement available from tighter proof tactics.
This construction is a scalar algebra test, not an accepted Aspis forgery.

Do not spend another iteration extending the fixed-target theorem without a
specific source obligation requiring it. The main blocker remains accepted
adaptive branches that the current K14 provider discards.

## Proposed mathematical organisation: condition at the query boundary

This is a generic counting reorganisation, not a new recovery theorem or a
claim that existing curve bounds are already sufficient.

Let pi be the complete ideal-interactive prefix immediately before the fresh
direct uniform q-subset of T query fibres. Include all prover randomness and
responses needed to fix the actual claimed final256 and the authenticated
virtual folded word. Gamma, alpha and the final polynomial may depend
arbitrarily on their earlier histories. No target is assumed fixed before gamma.

For each such prefix define:

- B_pi: fibres where that ACTUAL virtual folded word equals that ACTUAL claimed
  final polynomial;
- M_pi = |B_pi|;
- O_pi: a precisely specified pre-query event of failure of the chosen
  compatible-family representation/extraction description.

Crucial prerequisites:

1. B_pi and O_pi must genuinely be measurable from this prefix, with the ideal
   authenticated full-oracle model and actual final-value/index correspondence
   explicit. They are not inferred merely from a Merkle root.
2. The conditional query distribution given the whole prefix is uniform over
   distinct q-subsets. It is not enough for the marginal distribution to be
   uniform. A Fiat-Shamir adversary that prequeries/retries is not automatically
   in this ideal experiment.
3. If the current provider-none/width29 event depends on queries or later replay,
   it cannot simply be renamed O_pi. Construct a valid prefix-determined
   partition or a proved inclusion and account for any extra event. If that
   cannot be done, state the obstruction instead of assuming measurability.
4. Final terminal acceptance must be connected to pointwise query agreement or
   a proved batch/late-relation/authentication failure event. Neither the
   shifted-batch polynomial nor the pointwise query predicate is full acceptance.

Under these conditions, writing P for all POINTWISE folded query checks passing,

    Pr[P and O] = E[1_O * choose(M_pi,q)/choose(T,q)].                 (1)

The finite uniform-prefix version is just

    sum_{pi in Omega, O_pi} #{S : |S|=q and S subset B_pi}
      = sum_{pi in Omega, O_pi} choose(M_pi,q).

Use weighted prefixes or uniform master tapes if the prefix distribution is
not uniform. Do not silently replace it by uniform gamma/alpha.

### Tail formulation

For 1 <= q <= T set H(t) = Pr[O and M_pi >= t]. The exact identity is

    Pr[P and O]
      = sum_{t=q}^T [choose(t-1,q-1)/choose(T,q)] * H(t).             (2)

Derivation: choose(m,q)=sum_{t=q}^m choose(t-1,q-1), followed by finite sum
interchange. The current public mathlib documentation provides
`Nat.sum_Icc_choose` in `Mathlib.Data.Nat.Choose.Sum`; check the pinned cache's
version and use an equivalent local identity if necessary. Do not enumerate
T or QM31 during kernel reduction.

A coarser verified partition can be sufficient. For intervals with upper
endpoints m_j, charge

    sum_j Pr[O and M in interval_j] * choose(m_j,q)/choose(T,q).

These expressions correctly weight low-agreement bad prefixes rather than
charging them as automatically accepted.

## The work that would actually improve security

Proving (1)/(2) alone does NOT advance the adaptive recovery bound. The main
research target is a quantitative H(t), or a sufficient coarse-bin bound,
UNIFORM OVER ALL ADMISSIBLE ADAPTIVE PROVER STRATEGIES.

Connect it to the actual K14 width29 failure, not only the branches where a
provider already returns a witness. Reuse old curve/list/relation results only
where their hypotheses and events apply. Classify covered-valid, covered-invalid
and outside candidates; preserve early semantic and adaptive-C2 causality.

A close family's support LOWER bound is not an upper bound on M_pi. Do not
insert its cardinality into a far-target binomial bound without classification.
A mathematically finite/noncomputable family is not yet an efficient extractor;
retain its construction/resource obligations in any final AoK statement.

If only Pr[O] <= epsilon_old is known and M may equal T, (2) gives at best
epsilon_old. The identity does not improve the old ~75-bit bound on its own.
At least some new information controlling the agreement of accepted outside
candidates is required. Do not set H to zero by assuming candidate membership,
OOD-compatible existence, shared support, or successful provider return.

## Required regression cases and limits

Cover the original single-extra-fibre root-product construction and the
paired-extra-fibre variant, including any shifted-quartic/full-degree variant
already present. Do not keep lowering the family floor just to absorb examples.

Their all-zero-fibre subevents are useful exact tests, but M_pi includes ALL
folded cancellations, not just locations whose four unfurled values are zero.
Using the known zero-fibre count as an upper bound on M_pi is invalid without a
proof of the other cancellations. Their zero reference target is not a payment
witness. Full acceptance involves more than matching zero fibres.

Include a freshness countermodel: T=4,q=2, a target chosen after seeing S with
B_pi=S passes always, while the false application of (1) yields 1/6. Use it to
reject a misplaced conditioning boundary. It is not an Aspis attack.

## Source and probability composition

Aim for an explicit accepted-error inclusion/bound of the form

    accepted invalid/extraction-failing execution
      -> covered-case error OR outside-pointwise event OR batch error
         OR later relation error OR authentication/source/compiler error.

Translate this into probabilities without double-counting existing categories.
Do not condition on absence of a cryptographic failure in a way that silently
changes the query law. Use an explicit coupling/event inclusion.

The fixed-target numerical screen using q22, general rho cancellation and the
recorded 396430 inventory is 104.2667058229 bits. It is not the bound for the new
adaptive partition. Recompute the whole ledger when its events change. Do not
use any positive PoW credit. The programmable/lazy-ROM resource lift remains
separate; an ideal fresh query is not a newly proved deployed transcript step.

## Deliverable / stop condition

Use one small generic finite-count leaf if helpful, then concentrate on a
source-shaped outside-event bound. Provide either:

- a proved, genuinely new quantitative restriction on H(t) (or interval mass)
  for the actual adaptive candidate family, plus the remaining gap to 100 bits;
- or a precise counterexample/obstruction explaining why the attempted
  restriction fails, with the unknown accepted outside mass still visible.

Do not report another generic identity with an assumed tail envelope as a
security repair. No new source acceptance, new deployment, wholesale SBF build,
new size allowance, or large parameter sweep is authorised by this work order.
