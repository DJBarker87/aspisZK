# Regular layer cake: checked finite-sum interface

[GenericRegularLayerCake.lean](experiments/GenericRegularLayerCake.lean) is
GREEN on focused NUC v2: exit 0, 1.93 seconds, 3,297,932 KiB peak RSS, zero
swaps. Eight axiom audits contain only `propext`, `Classical.choice` and
`Quot.sound`. One harmless unused `alphaNonempty` warning is retained.
No unchanged replay, compiler-limit change or source edits after green.
This is a finite counting theorem, not the completed selected source adapter
or a Fiat--Shamir probability theorem.

V1 is retained: exit 1, 10.58 seconds, 3,281,464 KiB, zero swaps. Its errors
were an unparenthesized summand subtraction, unreduced `if True`, and two
addition-order applications. V2 changes only that proof glue. Dependent
`sorryAx` reports in the failed run are not proof credit.

## Exact formula and normalization

For a factor multiset s, original gamma finset Gamma, alpha-independent
predicate active(F,gamma), and support table m(F,gamma) in [L,U] on active
pairs, define the multiplicity-preserving count

    H(t) = sum_F card { gamma in Gamma : active(F,gamma) and t <= m(F,gamma) }.

`factor_gamma_layer_cake` proves the literal factor-by-gamma identity

    sum_F sum_gamma (if active then b(m(F,gamma)) else 0)
      = b(L)*H(L) + sum_{t=L..U-1} (b(t+1)-b(t))*H(t+1).

The identity needs no monotonicity. `layer_mono` substitutes an upper tail B
when b is monotone and b(L)>=0. Duplicate factor occurrences remain counted.

`factor_gamma_alpha_bound` directly consumes an alpha-dependent score table
and per-factor conditional moments

    mean_A score(F,gamma,.)
      <= if active then beta(m)+(1-beta(m))*epsilon else 0,
    beta(m) = choose(m,q)/choose(T,q), epsilon = min(1,3/|A|).

Its conclusion bounds the actual sum of these alpha means over factor and
gamma pairs, divided by the original |Gamma|, by

    (1-epsilon)*layer(beta,L,U,B)/|Gamma| + epsilon*H(L)/|Gamma|.

The score may depend arbitrarily on alpha. Neither active nor the support
table depends on alpha; no marginal-independence assertion is used.
`factor_gamma_alpha_conservative` requires Gamma.Nonempty, A.Nonempty,
A.card=k and B(L)<=Gamma.card, deriving a conservative single 3/k alpha
charge. This comparison concerns the SUM of factor incidences, not a union.

## Selected arithmetic and off-by-one checks

Here T=262144, q=22, L=9558 and U=200807. The same-Q support transfer is
4*m<=originalSupport.card+2. Thus the original-symbol threshold is 4*m-2,
and its incidence denominator is (4*m-2)-1024=4*m-1026, positive throughout:

    B(m) = floor(251238108102656/(4*m-1026)),
    251238108102656 = 1048576*239599331.

At L the denominator is 37206; B(L)=6752623450, remainder 21956. At U it is
802202. `selected_minimum_floor` checks the minimum arithmetic in Lean.
`beta_increment` requires q>0 and gives the increment choose(t,q-1)/choose(T,q).
Consequently the exact selected upper numerator is

    B(9558)*choose(9558,22)
      + sum_{m=9559..200807} B(m)*choose(m-1,21).

For one support m=3, L=2 and q=2, the unnormalized identity is 3=1+2:
using choose(3,1) as the increment gives 4, while excluding U gives 1.
For q=0 the general identity remains valid but the q-1 increment does not.

The selected k=(2^31-1)^4 equals
21267647892944572736998860269687930881. Hence B(L)<=k-1 holds for the full
nonzero gamma domain; it does not hold for every arbitrary gamma finset.
Likewise 3/|A| is not automatically 3/k for a smaller alpha set. A bounded
exact-integer check of the displayed sum, divided by
(k-1)*choose(262144,22), gives approximately 104.170846041 bits. Adding the
conservative 3/k gives 104.170841395 bits. These are one-row finite-moment
arithmetic diagnostics, not a new global soundness or sampler claim.

## Exact remaining selected instantiation

The C1-owned selected integration is separate; this agent did not edit it.
Its required construction, rather than an extra algebraic assumption, is:

1. Fix early C1, actual C2, completed OOD data and one common row before
   gamma. `CommonRegularRow.common_row` supplies a row and nonzero derivative
   product outside the full pre-OOD pair-root exception. Do not select rows
   separately per gamma while spending only one row's tail budget.
2. Let active(F,gamma) mean retained F and existence of some actual low
   regular prefix over all later kappa/tau/alpha histories. Choose its Q via
   `low_regular_witness`, obtaining support in [9558,200807]. Regular
   uniqueness identifies every later witness at this F/gamma with that Q;
   this is not a restriction that the adversary fixes its final before alpha.
3. `regular_fibre_tail_mem` sends each same-Q threshold m into
   supportGammas(...,4*m-2). Sum these inclusions with multiplicity and use
   `SelectedRegularTailSum.tail_sum_bound`; positive division derives tails.
4. `low_regular_moment` and `full_query_mass` discharge the generic moment
   premise for every fixed kappa/tau. Outside active there is no low prefix,
   so every score is zero. This chosen-representative argument must be made
   explicitly across all later histories, not just the history used to choose Q.
5. The nonnegative UNION score is at most the summed factor scores. Commute
   the finite means and use `shared_suffix` on the UNION once, adding only
   q/|G|+18/|A|. Keep A, semantic-repair G and Gamma distinct. The actual
   source sampler/ROM coupling remains outside these finite theorems.

## Falsified combination rules

- One gamma, two factors and seven alphas with disjoint matching triples:
  each factor costs 3/7, but their union costs 6/7. Hsum=2; Hunion=1.
  Substituting Hunion into the alpha correction is false.
- Event and matching mass both equal 1 at one of two gammas, 0 at the other:
  the joint mean is 1/2, not the product of marginals 1/4.
- Two factors active on opposite gammas each have average 1/2; their union
  average is 1, not the maximum of the factor averages.
- Conditioning A on the actual selected post-alpha event changes the cubic
  denominator. Keep that indicator inside the original alpha average.

These falsify combination rules, not the selected protocol. The common-row
pair-root exception may be witnessed by different factors at the two points.

## Pins and retained evidence

Inspected research revision: af75ce61c45f75bb0698647ad700732b068d8027.
Inherited runner creation pin remains 289d7356c78a4cd493fe61a54f9548f2a0c11298;
borrowed V7 pin remains 26a9cd4718aae9f9de7ef1c3394fb74a229085d5.
Lean4.32.0, -j1 -M9500, High8GiB/Max10GiB/Swap0/CPU200%; both v2 provenance
passes report 965 registered entries unchanged. This is not a package replay
or a claim that the historical registry is a complete imported closure.

| Artifact | SHA256 |
|---|---|
| Source and v2 snapshot | a974aa8e70ae3583f197819cf9d0bdc6062fdb79dc5c527a9e00dd08780592c4 |
| Green olean | f1fc2636ec67fb73c51be5ca6468088575845b62bd5fda16b95b28ac74301d4d |
| v2 manifest | 82e99c60b42d7603e311f93d572aa49a249f237ece8c79b8c5773a4a8bb75f2c |
| v2 log | 23ff38e58ff8ab73c3b7556ee661ab7d1524909a3f16488d250ecafc4684bd5d |

Both attempt source/log/manifest triplets and the green output are retained
locally. Final hashes were read from these artifacts; no new build was run.
