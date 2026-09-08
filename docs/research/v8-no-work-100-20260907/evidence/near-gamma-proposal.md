# After a33f4f6b: review and proposed near-anchor gamma binding

Reviewed pinned revision: `a33f4f6b2a11b52680597a5f849a63fe221f3fcb`.

## Evidence and scope

I inspected `row-binding-review.md`, `RowSeparatedImageGame.lean`, the preceding
`robust-recovery-review.md`, the source `v6_transcript.rs` preparation, the
`V7InactiveClaimBinding.lean` premise, and the concrete overlap theorem used in
`V7FixedWidth29TupleList.lean`. I independently calculated the body and local
bounds and executed the accompanying standard-library Python script. I did NOT
run Lean, Rust/SBF, or a payment verifier. No repository writes were made.

This package develops a **proposed mathematical argument** for a narrower next
step: pre-gamma representation and individual point-claim binding when there is
an image-valid quotient anchor within B=9301 complete fibres. It specializes the
support-interpolation argument from the earlier high-agreement package directly
to the original gamma-batched word. It does not repeat the first/fold stage of
that earlier proposal. It is NOT yet kernel-checked or source-connected.

It leaves the no-near-anchor event, valid-witness extraction, full-view ZK,
Fiat–Shamir/resource lifting, and CU parity unresolved. Do not call its numerical
screen a global Aspis security level.

## 1. The row repair is necessary for this proof route

Pinned ordinary assembly:

    gamma; absorb inactive_claim; kappa
    C = inactive_claim + row0 + kappa*row1 + kappa^2*row2.

The inactive term and row0 share a coefficient, so errors (-d,d,0,0) cancel
identically. Distinct bytes/domain labels do not fix an algebraically missing
random coefficient. The research repair instead uses:

    C = inactive_claim + kappa*row0 + kappa^2*row1 + kappa^3*row2.

For fixed pre-kappa errors i,e0,e1,e2, a nonzero error tuple produces a nonzero
polynomial of degree at most three. The special cancellation becomes
(kappa-1)*d. The row theorem then composes this with the noisy-word causal game;
it does not stop at a fixed-polynomial root bound.

The old V7 theorem explicitly states that an independently exact inactive
functional is required. This is not a newly refuted conditional theorem. What
needs a separate source audit is whether any actual accepting V7 path establishes
that premise independently. A passing source-shaped V8 research fixture is not a
production forgery; equally, 'production unchanged' is not evidence of enforcement.

The corrected research callback is still expensive in ways not reflected by
'one extra multiplication': the report states that it constructs/transposes dense
weights and hashes 16,384 public weight bytes before tau. That is not extra proof
body but it is real computation. No total CU saving is inferred here.

## 2. Exact numerical reproduction

Let p=2^31-1, k=p^4, T=262144, q=22. The committed restricted row bound is

    eps_row(B) = 25/(k-1) + 24/k + choose(B+255,22)/choose(T,22).

At B=9301, B+255=9556 and -log2(eps_row)=105.1452753728.
It uses 2.8256461614% of a 2^-100 budget. The remainder is only an arithmetic
ceiling before the currently unbounded terms; it is not a global residual budget.

The exact body formula is

    697*16 + 52 + 24 + 22*621 + 2*296*26 = 40282.

## 3. Proposed dense-curve cover: no target supplied as a premise

Work over a field K. Let C be a K-linear code with T vector-symbol positions.
Any two distinct codewords agree on at most delta positions. Vector symbols allow
a complete four-point fibre to count as one position. Fix arbitrary received
coefficient words v_0,...,v_(r-1), with NO assumption that these are codewords.

Define

    v(t) = sum_(ell=0)^(r-1) t^ell v_ell,
    Good = { t in G : exists c in C, dist(v(t),c) <= B }.

Here G is a fixed finite parameter set of distinct field elements. Good is defined
from the entire received curve and the code, not from the actually sampled gamma,
OOD answers, relation claims, decoder selection or later final polynomial.

For m>=r and

    b = floor(m*(T-B)/T),

assume the strict certificate

    T*choose(b,r) > (B+delta)*choose(m,r).                  (1)

Then either |Good|<m, or there exist codewords p_0,...,p_(r-1) such that:

- EVERY c within B of v(t), at EVERY t in G, is sum t^ell p_ell;
- the received coefficient tuple and p jointly disagree on at most
  floor(m*B/(m-r+1)) positions;
- the curve can be chosen from the fixed received words alone, before the actual
  parameter and all later responses. A canonical mathematical choice is not yet
  an efficient extractor.

### Derivation of the common support

If |Good|>=m, choose m distinct parameters and one close codeword at each. Let
S_j be their agreement sets. For every position i, let n_i count how many of these
sets contain it. Then sum_i n_i >= m*(T-B).

The integer sequence choose(n,r) is discretely convex: its successive difference
is choose(n,r-1), which is nondecreasing. Balancing two integer loads whose gap
is at least two cannot increase the sum of these binomial values. Thus

    sum_i choose(n_i,r) >= T*choose(floor(sum_i n_i/T),r)
                         >= T*choose(b,r).

Double count the left-hand side by r-subsets of the chosen parameters. By (1),
some r agreement sets have common intersection S with |S|>B+delta.

Interpolate their codewords in t. The coefficient words of the interpolant
belong to C by K-linearity. On S the interpolant P(t) and received curve v(t)
agree at r distinct t-values and have degree at most r-1, so agree identically.

Any other c with dist(c,v(t))<=B agrees with P(t) on at least |S|-B>delta
positions. Therefore c=P(t). This proves coverage of arbitrary close candidates,
including candidates chosen after the actual t, without an assumed candidateMember.

### Own-support recovery, not same-support recovery

At a position where at least one scalar coordinate of some v_ell-p_ell is nonzero,
the difference v(t)-P(t) has at most r-1 roots among the selected m parameters.
That position contributes at least m-r+1 disagreements. The total is at most mB.
Therefore the number of jointly mismatching positions is <=floor(mB/(m-r+1)).

This support is NOT assumed to equal or contain every cancellation position in
one selected combined candidate. The root-product examples retain their extra
matching fibres and their same-support failures.

## 4. Specialisation to B=9301

Use the original circle code viewed as full four-point fibres:

    T=262144; delta=256; r=29; m=64; B=9301.

The delta=256 bound requires the concrete injective/disjoint four-point fibre
mapping: 257 full-fibre agreements give at least 1028 distinct symbol agreements,
contradicting the existing 1024 root/overlap cap. This source/encoder bridge is an
obligation, not inferred just from saying 'arity four'.

The balanced load is 61, and the exact averaged common-support lower bound is

    T*choose(61,29)/choose(64,29)
      = 3829760/93 = 41180.2150537634... > 9557 = B+delta.

The coefficient mismatch cap is

    floor(64*9301/(64-29+1)) = 16535.

So the represented component tuple jointly matches at least

    245609 complete fibres = 982436 individual positions.

That is its own support. The C1 base-field descent theorem has ample cardinality
margin, but its exact projection/source interface must still be instantiated.

If fewer than 64 nonzero gammas are good, the ideal gamma event has probability
at most 63/(k-1), even when the subsequent proof is chosen adaptively. This bound
must be charged BEFORE conditioning on the near-anchor event.

If at least 64 are good, the cover supplies a fixed component tuple for EVERY
near original-code candidate. Given an image-valid quotient anchor Q within B
of the virtual quotient, U=LQ+I is such an original-code candidate: multiplication
by a nonzero chord denominator preserves all off-noise equality positions.
Therefore U=sum gamma^ell p_ell. This implication needs image validity; the T512
invalid-image example belongs to the separately handled image case.

The original-code curve and recovered tuple depend on C1/C2 received words,
which are fixed before gamma. C2 may depend on lambda/chi. Do not use this fact to
pretend the full tuple was fixed before lambda/chi; early semantic causality is
another bridge. The tuple does not depend on the actual OOD responses or gamma.

## 5. How this can turn three row equalities into 87 point equalities

Freeze the three point functionals ell_j and their 87 claimed component values
c_(j,l) before gamma, as in the intended order. In the large-Good case above,
define component errors

    a_(j,l) = c_(j,l) - ell_j(p_l).

These are fixed BEFORE gamma. If any error is nonzero, choose one erroneous row
j deterministically. Its aggregate residual

    E_j(gamma) = sum_(l=0)^28 gamma^l a_(j,l)

is a nonzero polynomial of degree at most 28. At most 28 nonzero gammas make it
zero. For every other gamma at which an image-valid B-close quotient anchor exists,
that anchor's reconstructed original is the represented p(gamma), so its actual
row error is E_j(gamma), not an unrelated post-challenge residual.

The inactive error may still depend arbitrarily on gamma, but is fixed BEFORE
kappa. The corrected row polynomial has a nonzero point coefficient, regardless
of this inactive error. The proved restricted row/noisy bound applies at that
prefix, permitting adaptive later responses.

Thus a proposed bound for

    relation acceptance AND image-valid B-close anchor exists
    AND (pre-gamma curve cover absent OR some claimed component point is wrong)

is

    max(63/(k-1), 28/(k-1) + eps_row(B)).                  (2)

The two cases are disjoint according to the size of Good, fixed before gamma;
there is no conditional-uniformity assumption on gamma after observing existence
of a near anchor. For B=9301, the second term dominates and (2) equals

    53/(k-1) + 24/k + choose(9556,22)/choose(262144,22)
       = approximately 2^-105.1451901644.

This is a PROPOSED combination of the mathematical cover and the committed
restricted row theorem, NOT a new Lean or source result. Its absent-cover branch
is explicitly retained. It is not the false statement that every received word
admits a near anchor or that every accepting execution belongs to this class.

No 100-target union is used. No new protocol query, transmitted interpolation
point, field or domain change is introduced. The 64 challenge values are analysis
objects; finding them efficiently is a separate extractor-resource task.

## 6. Remaining boundaries

Even if formalised, (2) binds component point claims only in the near,
image-valid class. It does not establish:

- a numerical bound on accepted executions with no B-close quotient anchor;
- validity of the recovered tuple as a payment witness or early semantic/copy
  claims, including C1-before-lambda/chi causality;
- an efficient extractor obtaining the mathematically chosen curve;
- full transcript/kernel source refinement, fresh-query/Fiat–Shamir lifting,
  replay resources, full-view zero knowledge, or complete-transaction CU parity.

The far original/paired root-product cases remain outside the useful near class.
The high-J case is compatible: its zero tuple has its own common support and its
combined codeword can acquire extra cancellation fibres. An existence proof of
that zero tuple is still not an ownership witness.

The permitted size remains exactly 40282. Public weight hashing, research
transcript framing and event overlap must be accounted for. In particular do
not add eps_row again to an event ledger already covering those same rounds.

## 7. Checks executed

`python check_near_gamma.py` produces `results.json`. It performs:

- exact full-parameter certificate, own-support and body arithmetic; the binomial
  query ratio is independently checked as a falling-product rational;
- 6561 received curves with two coefficient words over alphabet {0,1,2} in F5^4,
  enumerating every constant-code candidate at every nonzero F5 gamma; 297 take
  the constructive cover branch, with 1188 actual near candidates covered;
- all 15624 nonzero 3x2 component-error arrays over F5, maximizing the adversary's
  pre-kappa inactive error separately for each gamma, and checking the combined
  gamma/kappa root budget (62000 nonzero gamma-row cases); the sharp two-stage
  cap is attained;
- the explicitly forbidden after-kappa inactive choice, which cancels every case;
- a high-J root-product toy that recovers the zero tuple on its own support while
  preserving eight same-support failures.

These checks are exhaustive only over their stated small domains. They do not
certify a 2^-100 probability by experimentation, and they are not production
field/source execution. The run evidence records this workload, not proving time.

## Sources inspected

Pinned repository paths (all at a33f4f6b...):

- `docs/research/v8-no-work-100-20260907/row-binding-review.md`
- `docs/research/v8-no-work-100-20260907/experiments/RowSeparatedImageGame.lean`
- `docs/research/v8-no-work-100-20260907/robust-recovery-review.md`
- `crates/aspis-core/src/v6_transcript.rs`, lines 690–750
- `AspisFormal/AspisFormal/Pool/V7InactiveClaimBinding.lean`
- `AspisFormal/AspisFormal/Pool/V7FixedWidth29TupleList.lean`, lines 55–130

The generic support-interpolation construction specializes the earlier
`aspis_v8_high_agreement_review.zip` proposal; that proposal was not treated as a
Lean-certified result. Mathematical library references (check pinned versions):

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Lagrange.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Roots.html
