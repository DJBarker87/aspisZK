# Three helpers, wrong C1 OOD claims, and adaptive final steering

Research base: `edb199c12fcc41f00330298b95b4736f60ac6f3a`. Work here is a
reduced causal strategy experiment, not a protocol change or a QM31 bound.
The committed F11 `final_transport_strategy.rs` is not rerun or modified.

## The new question

The previous experiment showed that selecting the final after alpha changes
the carried scalar too. It did not use an actual circle domain, a chord
derived from OOD points, or the false-C1-OOD reciprocal-power term. The new
question is whether an adaptive final can exploit that scalar freedom on
prefixes with **no nearby image-valid quotient**, when the received data
has the actual three-helper-plus-known-C1 form.

The experiment fixes zero C1 and three specified helper words before a
reduced OOD challenge. In the non-polynomial profile, each helper is
supported on its own predetermined circle fibre. The zero-helper profile
is a separate rational-word control. Both C1 lane-zero OOD answers are the
fixed false value 1, while every other component answer is zero. Thus the
interpolant is the constant circle polynomial 1.

For each nonzero gamma the normalized virtual received word is literally

```
(H + gamma*G + gamma^2*D)/L - gamma^(-26)/L.
```

No quadratic-curve theorem is applied after deleting the last term. A
deliberately invalid comparison deletes only that term and remains labeled
as such. Gamma normalization is an invertible change of variables in this
fixed finite strategy family, not a source of security bits.

## Reduced geometry and exact interfaces

The field is F19. Its four nonzero signed circle fibres give 16 distinct
stored points, with four distinct final coordinates `T2(x)=2*x*x-1`. The
quotient's eight natural basis entries are

```
[1,y,x,xy,T2,y*T2,x*T2,xy*T2].
```

The fresh two-mode reduced OOD experiment uses the axis pairs
`(0,1),(0,-1)` and `(-1,0),(1,0)`. The literal source cross product gives
`L=2x` and `L=2y`, respectively. Those factors are retained in denominators,
chord transport and the second image functional; no unproved transcript
rescaling is invoked. All selected stored points are nonpoles for both
modes.

A polynomial-pair reference first multiplies by the actual chord, converts
the result to the natural basis and projects to the eight carried entries.
The optimized transpose is compared with that dense reference. The two
image equations are `[Q7,2Q6]=0` for `2x`, and `[Q7,-2Q5]=0` for `2y`.
Image-valid inputs are also compared by literal polynomial evaluation, so
truncation cannot conceal a nonzero omitted term on that class.

The four-slot primal fold and the source-shaped dual order
`[1,alpha^3,alpha^2,alpha]/4` are retained. All `19^2` final coefficient
pairs are available after alpha. Their final code is linear in `T2(x)`.
The three ordinary product rows have shifted powers and a nonzero fixed
inactive covector. These are explicitly reduced product rows, **not** the
selected ten-coordinate payment semantic/successor assembly.

The scalar is corrected by the actual functional of the interpolant:

```
claim = gamma^(-26) * (inactive - ordinary(kappa)[0]).
```

A constant circle polynomial is coefficient vector `e0`; an MLE functional
does not generally evaluate it as 1. The first preflight rejected my
incorrect row-scale-sum assertion at precisely that distinction. The
failed log is retained; the actual `w[0]` correction replaces it.

## Causal strategy space and classifier

| Boundary | Fixed or permitted choice |
|---|---|
| Before the reduced OOD mode | Zero C1 and both fixed helper profiles; fixed false component OOD answer rule |
| After OOD mode and gamma | Inactive scalar may adapt |
| Fresh kappa, then fresh tau | Ordinary/image weights determined from the same chord and fixed rows |
| Before alpha | First compact response: free `c0,c1`; `c2,c3,c5,c6=0`; `c4=claim/4-c0` |
| After alpha, before queries | Any of the 361 final coefficient pairs |
| Fresh ordered distinct query pair, then nonzero rho | Literal discrepancy `prior - rho*(r0+rho*r1)` |
| Three subsequent fresh relation challenges | Reduced degree-six discrepancy game, with its exact six-root repair optimum |

The first-response family is restricted; this is not exhaustive over all
possible prover strategies. Later repair attainability is checked by an
explicit six-root polynomial with nonzero compact boundary and scaling to
every nonzero prior. These are three abstract compact discrepancy rounds,
not a claim that the 8-to-2 toy vector has the selected 1,024-to-4 dimension
sequence. The toy model retains the causal boundary and scalar grammar,
not all production semantics.

The actual fixed prefix's distance to an image-valid quotient is computed
without presupposing a candidate. For every one of the 16 fibre subsets,
solve the natural-encoder equations plus both image equations. Feasibility
of the largest support gives the exact nearest image-valid quotient
distance in this reduced code. This classifier is separate from the
chosen final's distance from the actual folded word.

Two controls distinguish unrestricted scalar steering from requiring
`response0(alpha)-<foldedWeight,final>=0` before query injection. The latter
is a smaller legal final strategy family, not an implied property of
acceptance. A single carried linear equation ordinarily leaves an affine
hyperplane of final coefficients; it cannot be treated as a final-identity
test.

## What the completed preflight establishes

[helper_ood_strategy.rs](experiments/helper_ood_strategy.rs) currently
enables only a tiny fixed-prefix preflight. No full causal average has yet
been run or claimed. The preflight exhausts finals and the displayed
first-response family at its predeclared prefixes; it is not a search for
favorable challenge transcripts. Fresh query sampling uses all 12 ordered
distinct pairs, not six sorted pairs.

The corrected [v2 log](experiments/helper-ood-strategy-preflight-v2.log)
passes 9,104 dense/reference checks and 6,840 direct scalar-versus-histogram
checks. Both profiles, both chord modes and each predeclared gamma in
`{1,2,3}` have **exact nearest image-valid quotient distance 3 of 4 fibres**.
That is stronger evidence than merely finding a far final: these prefixes
really lack an image-valid quotient within one or two fibres in this
reduced code.

The 456 states are exactly

```
2 helper profiles * 2 chord modes * 3 gammas
  * 2 predeclared (kappa,tau) pairs * 19 initial claims.
```

For every one of them, backward induction over the 361 permitted first
responses, all 19 fresh alpha values and all 361 adaptive finals gives a
strictly greater optimal far-final score when the pre-query carried prior
may be nonzero than when it is required to vanish. All ordered query/rho
outcomes and the exact reduced tail value are counted, not selected
favorably afterwards. The claim is treated as an input fixed before the
response; checking every claim does not give the prover permission to
choose it after kappa or tau.

This falsifies the proposed **without-loss-of-generality restriction**
that an optimal far-final continuation can first force
`response0(alpha)-<foldedWeight,final>=0` and then analyze only pointwise
query agreement. The future shifted query batch can legitimately cancel
a nonzero carried discrepancy, and optimal adaptive policies can exploit
that interaction. It does not falsify the corrected source/game theorems,
which already retain that discrepancy and its cancellation event.

The 456 count is not 456 attacks, an acceptance fraction, or a payment
forgery. The data comprise conditional strategy optima on predeclared
prefixes of a restricted reduced game. They do not enumerate all gamma,
kappa and tau values or the earlier inactive choice, and hence are **not
an unconditional averaged wrong-C1-claim probability**. They also do not
cover arbitrary helper words or all six free first-response coefficients.

[helper-ood-strategy-preflight-v1.log](experiments/helper-ood-strategy-preflight-v1.log)
records optimized compilation exit 0 (1.04 s, 134,561,792-byte peak RSS,
zero swaps), then the failed affine-scalar assertion, exit 101 (0.41 s,
1,671,168-byte peak RSS, zero swaps). No checks were weakened to suppress
that discrepancy. The source was corrected to the literal `w[0]`
interpolant contribution; query ordering and both factor-two source chords
were checked before the successful v2 run.

| v2 stage | Exit | Wall | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Optimized `rustc -O -C overflow-checks=yes` | 0 | 1.16 s | 136,511,488 bytes | 0 |
| Tiny fixed-prefix preflight | 0 | 0.52 s | 3,129,344 bytes | 0 |

The program's internal timers recorded 0.079886290 s for histograms,
0.012014291 s for conditional final-state optimization/direct checks, and
0.004054503 s for first-response optimization; total internal elapsed time
was 0.097908416 s. These are host reduced-search measurements, not proving,
extraction or verifier CU.

Source SHA-256:
`322056c4ceba5ae1c18391386ade43b50695cb4ecc2a839a0eac8ad6069da9db`.
Runner SHA-256:
`bcde5240ce5ffce84e7abece91311c1b4507065ae39f7f8ea414d77d7eaeda73`.
The source remains frozen at the successful preflight revision.

Reproduce from the research worktree with an unused log path:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_helper_ood_strategy.sh \
  /tmp/helper-ood-preflight-new.log
```

This compiles only the standalone optimized Rust file, using recorded
`rustc 1.93.0`; there is no package build or new Lean result in this artifact.

The runner has a 1-GiB process-tree guard and a 90-CPU-second child limit.
No Lean replay, SBF, full transaction, witness extraction, prover run or
source change outside this isolated experiment was performed. The accepted
proof body remains 40,282 bytes.

## One bounded next enumeration

A full average **within this same restricted strategy family** would use
all 18 nonzero gamma values, all 18 nonzero kappa/tau values, and maximize
the inactive scalar before kappa. It must then report wrong-C1-OOD accepted
mass on the no-image-anchor prefixes separately from the chosen final's
distance, including the deliberately invalid omitted-reciprocal control.

Keeping both helper profiles and both chord modes increases histogram
contexts from 12 to 72 (factor 6), and conditional `(kappa,tau)` contexts
from 24 to 23,328 (factor 972). Reusing the already precomputed compact
response schedules gives this measured-cost extrapolation:

```
6 * 0.079886290
 + 972 * (0.012014291 + 0.004054503)
 = about 16.10 seconds of internal search work.
```

This is an estimate, not a completed measurement or latency guarantee.
The final-state timer includes direct reference checks that would not be
needed at every full-sweep state, but the estimate does not credit removing
them. Histograms can remain sequential, so the larger enumeration need not
retain all gamma prefixes in RAM. A separate explicit grant, a 1-GiB guard
and the existing 90-CPU-second ceiling would bound that next experiment.
It has **not** been launched or implemented as an enabled runner mode here.

Even a high accepted wrong-OOD rate in this tiny field would not establish
a payment forgery or a QM31 rate. Conversely, recoverable zero C1 here is
not a proof that every decoded C1 satisfies payment semantics. The useful
output is a precise obstruction or surviving causal relation constraint
for the next symbolic far-final argument, with the reciprocal term and
actual image-aware scalar transport still present.
