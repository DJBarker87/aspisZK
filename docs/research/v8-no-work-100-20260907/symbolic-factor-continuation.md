# From symbolic OOD identities to a fixed factor family

Research-only continuation, 2026-09-10. Inspected parent:
`f0f46ffede8812252ac7cee9edf5547f228533d5`, on
`research/v8-no-work-100-20260907`. Newer/concurrent main work was preserved.
Lean ran on the NUC at the user's request; no laptop compilation, production
change, deployment, SBF rebuild, or unchanged full replay.

## Outcome

The primary new result is **not another derivative-only bound**.
`CausalFactorReduction.total_reduction` replaces the previously unrestricted
pair-of-symbolic-OOD-identities remainder with an actual reconstructed
polynomial root of a fixed, positive-Y, both-OOD-identity factor family.
It works for arbitrary received component words and adaptive final selection,
including repeated/singular interpolation parents. Its numerical ceiling is
unchanged; the remaining event is more specifically constrained.

For the SAME causal compact-suffix execution, Lean proves

```
totalProbability <= existing_missing_good_ceiling
                    + 117077 / |Gamma|
                    + factorProbability.
```

`factorProbability` includes honest accepted executions. It must NOT be
bounded as though all of it were extraction failure. The next security target
is its intersection with failure of the specified checked-payment extractor.
No completed global extraction/100-bit/security-release claim follows here.

The parallel deterministic result connects the literal selected copy layout
and its weighted row identities to the actual 136-link rational balance. This
advances the payment-constraint path, with its residual/helper/pole premises
still explicit. See [the copy-link report](selected-copy-link-balance-review.md).

## Why the new factor construction works

The nonzero trivariate interpolant `P(X,Y,Gamma)` is an analysis object chosen
from the fixed C1/C2 words before either OOD point. The two actual sequential
OOD answer rows determine degree-at-most-28 polynomials `A0`, `A1`, including
the literal GRS clearing factors `(1+t_r^2)^512`. They are not the separate
degree-two helper curve, which remains unchanged.

Factor P using the existing V7 prime-factor multiset. For each factor F,
before gamma is sampled:

- If F has positive Y degree and both `F(t_r,A_r(Z),Z)` are polynomial
  identities, retain F; its exception factor is 1.
- Otherwise, for a positive-Y factor choose one actual nonzero OOD
  substitution polynomial. A later candidate rooted in F and matching both
  actual OOD answers forces this polynomial to vanish at gamma.
- For a Y-constant factor, choose a nonzero X-coefficient polynomial in Z.
  A zero specialization of that factor forces this polynomial to vanish too.

Multiply these nonzero exception polynomials. The total degree is at most
the sum of the factors' Y/Z weights, which is at most P's weight, hence
**117077**. Repeated copies are included in that same additive budget. This
does not assume a square-free parent, a nonzero parent derivative, successful
decoding, or component membership. There is no additional factor-count,
content, or zero-specialization multiplier.

The product is fixed before gamma. For every later polynomial U, including a
different U at every gamma/alpha, a parent root matching both actual OOD rows
either belongs to a retained factor or hits a root of that one product.
The generic result is `FactorIdentityCover.exists_identity_factor_cover`.

The retained family has at most **111 positive-Y factors, counting
multiplicity**: the existing V7 positive-factor-cardinality theorem and
`curveTrivariatePolynomial_natDegree_lt` give degreeY < 112. This is a
derivation from existing checked results, not a new specialized cardinal
declaration. It is not a bound of 111 component tuples, and no 111-target
query union is introduced.

## Actual selected objects and causal connection

`SelectedIdentityCover.literal_candidate` derives, for one literal covered
image-valid Q, both the interpolation root and the two OOD equalities for
the SAME polynomial

```
U = exactCircleGRSPolynomial ((atGamma data gamma).original Q).
```

It consumes the completed quotient-to-original-symbol bridge and GRS/chord
identities. There is no substitution of a different existential candidate.
`exists_selected_cover` then constructs the exception polynomial from the
actual C1/C2 and actual OOD prefix, before quantifying over gamma or Q.

`CausalFactorReduction.factorPrefix` simultaneously requires this same Q to
be covered by the literal quotient family, image-valid and ordinary-row
correct, to fold to the actual post-alpha final, and to have U rooted in a
retained factor. Its exact accepted-mass accounting is:

| Class | Fixing time / treatment |
|---|---|
| No good covered quotient | Classified after alpha; existing uniform relation/query ceiling applies |
| Good quotient but no same-Q retained-factor root | Classified after alpha; derived implication to a root of the pre-gamma exception polynomial; at most `117077/|Gamma|` |
| Good quotient with same-Q retained-factor root | Kept as `factorProbability`; not renamed a tuple or payment witness |
| Authentication, actual source/sampler mismatch, replay abort/fuel/missing response/cached-advance mismatch | Outside this compact ideal-game theorem; still require the actual resource-bounded extraction coupling |

The prefix still fixes C1 before lambda/chi; adaptive C2 may depend on those
earlier challenges. P/factors fixed after C2 cannot be moved back before
lambda/chi to justify semantic/copy root counts. Both OOD responses retain
their sequential absorption order. Ordinary claims, shifted kappa rows,
carried tau image weights, response0 before alpha0, post-alpha final256,
queries before rho, and sequential later relation responses are unchanged.

## Reused and new theorem status

| Target | New checked result | What it does not prove |
|---|---|---|
| `CurveOODDerivative` | Actual first-Y Hasse row; degree <= 117049; specialized derivative interface | Nonzeroness of that derivative |
| `FactorCoherence` | One pre-gamma factor for all compatible adaptive candidates outside parent-derivative collisions | Coverage of singular parents or component recovery |
| `SelectedFactorCoherence` | Literal selected same-Q connection for that restricted regular case | A primary global bound; this derivative charge is NOT added to the family ledger |
| `RationalHelperIdentity` | Degree-27 helper control, OOD identities, compatible zero specialization, and no polynomial-in-X component curve for that control | Full semantic/commitment/payment execution |
| `FactorIdentityCover` | Constructed exception product and adaptive both-identity factor-family coverage, including content and repeated parents | Factor roots imply original-code component tuples |
| `SelectedIdentityCover` | Actual selected root/OOD interfaces and the 117077 cap | Merkle/replay access or payment extraction |
| `CausalFactorReduction` | Exact same-execution partition and quantitative accepted outside-factor bound | The remaining factor-and-failed-extraction probability |
| `SelectedCopyLinkBalance` | Selected endpoint uniqueness and weighted-row-to-link rational balance | Chi/lambda collision exclusion or acceptance enforcing its local premises |

Eight focused leaves passed, with 53 named standard-only axiom audits. The
number of declarations is evidence inventory, not a security metric. The
strong primary path reuses V7 factorization, weighted-degree additivity,
interpolation, and exact code/GRS bridges; it does not import the old large
recovery loss as a new security term.

## Falsification and remaining mathematics

The regular-parent approach was deliberately not used as the final repair.
An honest code curve U admits the multiplicity-three interpolant
`P=(Y-U)^3`; its derivative vanishes along honest OOD answers. Such singular
parents are not intrinsically rare or malicious. The family proof handles
them without charging parent singularity as a failure.

The new rational-helper control retains fixed early C1=0 and a degree-at-most
two helper curve. With `N(Z)=Z^26*(Z-b)` and `a` outside stored points, take
received normalized helper values yielding `N(Z)/(x_i-a)`. At legal OOD
points t, `A_t(Z)=N(Z)/(t-a)` is a degree-27 polynomial answer. At nonzero
gamma=b the compatible U is zero, although there is no global polynomial
component curve equal to that rational function. The elementary identities
and no-polynomial statement are Lean-checked. The `H^3` interpolation-kernel
embedding and argument for arbitrary kernel choices are mathematical
derivations in [identity-factor-review.md](identity-factor-review.md), not
claimed source/Lean/payment refinements. This demonstrates why even a
retained linear factor needs a charged specialization/recovery argument.

All earlier regressions remain: original/paired root-product shortcuts,
high-J own-support recovery, T512 invalid image, zero-fold image kernel,
unshifted-row cancellation, late-inactive timing, shifted degree-q rho and
later repairs, radius-boundary extraction, and the mixed-C1 minority-target
counterexample. This turn did not rerun unchanged regression suites or claim
that their remaining component/witness obligations disappeared.

## Ledger and costs

[symbolic-factor-ledger.json](symbolic-factor-ledger.json) is generated and
exactly checked by `experiments/symbolic_factor_ledger.py`. For ideal
`Gamma=QM31\{0}`, the new factor-cover term is `117077/(k-1)`, approximately
107.162902 bits. It **replaces** the old OOD-nonidentity term. The known
local reduction ceiling stays approximately **104.366053 bits**, with the
remaining factor/extraction mass explicit and unbounded. The derivative
117049 term, historical 396430 inventory, and four relation repairs are not
added again. Probabilities are summed before conversion to bits.

This is not a resource-independent or Fiat-Shamir result. Actual nonce/retry
selection, prequeries, forks, restoration/fuel and extractor running time
remain separate obligations; grinding security credit is zero. Classical
only; no quantum claim. Full-view ZK remains a separate simulator obligation.

No Rust, wire, protocol checks or public messages changed. The maximum body
remains exactly `697*16+52+24+22*621+2*296*26 = 40,282` bytes. No new CU,
proving-time, or RAM benchmark was run. The formal code's noncomputable
factor choices are not verifier operations or a practical extractor.

## Reproduction and evidence

See [symbolic-ood-build-evidence.md](symbolic-ood-build-evidence.md) and its
machine-readable audit/receipt. NUC overlay:
`/home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg`.
Pinned native cache and imports were reused; no dependencies were rebuilt.

```
ssh -o BatchMode=yes dombarker@nuc.local \
  'bash /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg/run_symbolic_ood_nuc.sh \
   /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg TARGET FRESH-TAG'
python3 docs/research/v8-no-work-100-20260907/experiments/symbolic_factor_ledger.py --check-recorded
python3 docs/research/v8-no-work-100-20260907/experiments/audit_symbolic_ood_evidence.py --check-recorded
```

Runner invokes the pinned `lake env` Lean with `-j1 -M9500` in its own scope:
MemoryHigh=8GiB, MemoryMax=10GiB, MemorySwapMax=0, CPUQuota=200%. Green leaf
wall times range 1.18–6.02 seconds; maximum individual RSS is 6,875,788 KiB;
zero swaps. These are focused proof-check costs, not prover measurements.
Source/olean hashes, imports, commands, exits and failed source snapshots are
retained. The regular selected bridge needed generic symbolic constructor and
root-transport helpers; increasing recursion depth did not fix it. Final
proofs retain depth200 there, with no giant normalization or new axiom.
The staged whitespace check reports five trailing-whitespace lines in two
raw failed Lean logs (`selected-factor-coherence` v1/v8); their original
bytes are preserved for hash verification. The staged non-log source and
documentation whitespace check passes.

A delayed agent launch caused a roughly two-second overlap between the first
failed derivative check and the green copy-link check. The journal is retained;
both jobs remained capped, but those timings are not fully serialized host
measurements and aggregate RSS was not sampled. Subsequent jobs were explicitly
serialized. Concurrent main-source drift in one borrowed V7 file was handled
by retaining its exact pinned git blob, not editing main or rerunning Lean.

## Decision and next experiment

Keep the QM31 q22 design as the soundness-research target; this continuation
narrows a real accepted adaptive outside branch without spending proof bytes
or security margin. It does not establish production readiness.

The single next experiment is a **retained-factor specialization-to-component
recovery lemma**, first for a retained linear-Y factor, with the rational-helper
pole control as a mandatory regression. It must either recover a coherent
original-code tuple on its own support or charge the exceptional gammas; it
must not demand polynomiality at every specialization. Reuse the tested
degree-one OOD local divisor and V7 weighted factor machinery, while keeping
early-C1 selection and payment validation separate. The unchanged old
fixed-branch Hensel threshold exceeds the available raw budget (see the
factor report); merely plugging it in is a stopping condition, not success.
