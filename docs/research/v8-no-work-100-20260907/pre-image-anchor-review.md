# Pre-image-challenge geometric anchor

Continuation from clean research checkpoint
`bbca32e0e30be2c489c6437dd670da164e6d852f`. No production, main, verifier,
wire, field/domain/query or mask changes are made by these leaves.

**Proof status:** the generic and exact selected-encoder dichotomies are
kernel checked. The focused B=2325 endpoint constructs a 9300-close anchor
or retains the sparse eligible branch. This is not yet a complete accepted
payment-extraction theorem.

## The new object is selected before tau

Let `R` be the actual received virtual quotient, fixed before the image
challenge. Define eligibility from `R` alone:

```
Eligible(R,B) = { alpha | exists final256 with at most B folded discrepancies }.
```

There is no provider, acceptance, row response, tau or actual disclosed
final in this definition. The finite-universe theorem takes a fixed alpha
set `A`. For the full-field ideal experiment, choose `A=univ` before tau;
otherwise its sparse conclusion only counts eligible challenges inside A.
The dense conclusion represents close finals at every alpha, not only A.
This alpha universe is not the 262144-point query-domain set used by the
relation game's fixed oracle.

Under `5B+255 < 262144`, the selected theorem gives a dichotomy:

1. At most three alphas in A are eligible. This is a sparse geometric
   branch, not an unconditional rejection assertion.
2. There exists one full natural1024 quotient coefficient vector `Q`,
   differing from `R` on at most `4B` complete fibres, such that **every**
   B-close final at **any** alpha equals `coefficientFoldLayer 256 alpha Q`.

The quantifier order is `R,B,A -> exists Q -> forall alpha,final`.
Because neither tau nor actual responses occur in those choice inputs,
the mathematical choice can be made before tau. It does not retrospectively
freeze the prover's final. The dense branch never assumes a supplied
anchor, candidate membership or exact received polynomiality.

The anchor is in the full quotient code. Its image validity and ordinary
point-row correctness are **not** conclusions of geometry alone.

## Why close final selection becomes fixed-anchor folding

The prior four-fold theorem constructs a full quotient within `4B` whenever
there are at least four eligible alphas. This new proof consumes that
result through its contrapositive; it does not replay interpolation or
impose a decoder/provider filter on the eligible set.

Fix such a quotient Q and any B-close final. Outside the union of the
anchor's at-most-4B complete-fibre errors and the final's at-most-B folded
errors, the final codeword and the actual fold of Q agree. The latter is
the codeword of `coefficientFoldLayer 256 alpha Q`, by the committed V7
circle-lift/fold commutation identity. Thus they agree at more than 255
actual final-domain points. The selected natural256 code overlap theorem
forces equality of their **coefficient vectors**, not merely equality of
some queried values.

The proof establishes the support inclusion using the literal four-slot
map and the normalized fold. It does not substitute a raw V7 gamma-batched
word for the V8 quotient or infer polynomiality of R.

## Focused parameter point and intended composition

For `B=2325`, the constructed quotient is within `9300` complete fibres,
inside the earlier `9301` near-anchor regime, and the guaranteed overlap
is at least `262144 - 5*2325 = 250519 > 255`.

This supplies the fixed-anchor/final-representation hypothesis for a
restricted joint image/relation game on B-close actual finals. It does not
condition away bad-image or bad-row challenges: those probabilities must
be charged by the corresponding causal game. A four-alpha interpolation
argument alone cannot establish a degree-six relation residual is zero.

There is also a timing boundary for row mixing. Pre-tau is not automatically
pre-kappa. The geometric object depends only on R; to use it in a kappa root
bound, the source/game constructor must establish that R's determining
inputs are fixed before kappa. The research preparation computes some chord
data later, but its gamma/OOD inputs are earlier; that source-dependency
argument must be connected, not replaced by a label-independence claim.

The sparse eligible branch contributes at most `3/k` only to executions
selecting a B-close final under a genuinely fresh uniform full-field alpha
conditional on the preceding prefix. A marginally uniform alpha or an
FS-selected/retried transcript does not establish that conditional law.

Finals farther than B remain explicit. The theorem does not assign their
acceptance probability the near-anchor ceiling or the sparse `3/k` bound.
The weak radius/query-only screen from the previous continuation is not
relabelled as a security result.

## Existence, resource bounds and remaining events

Selecting an anchor from all geometric possibilities uses classical
existence, not an implemented bounded decoder or replay extractor. The
theorem does not obtain four fixed-prefix transcripts from a Merkle root,
recover component-wise original-code membership, or return a checked
payment witness. Those implications and their resource costs remain open.

| Class | New information | Still required |
|---|---|---|
| Sparse eligible set; selected final B-close | At most three eligible alpha values | Full-field conditional law, actual source/replay coupling |
| Dense eligible set; selected final B-close | One pre-tau Q represents that final | Joint image/row rejection and image-valid component recovery |
| Selected final farther than B | No branch dropped | Quantitative accepted-recovery bound or legitimate extraction route |
| Provider/replay/fuel/authentication/source failure | Unchanged explicit residual | Total extractor accounting and resource-bound composition |

The proof body remains 40,282 bytes. There is no new transmitted message,
verifier operation, CU measurement, prover benchmark or security credit
from grinding. Full-view ZK and the resource-bounded FS lift remain separate.

## Focused proof map and evidence

| New theorem | Meaning |
|---|---|
| `PreImageAnchor.close_final_identifies_fold` | Actual normalized folds and final-code overlap force coefficient equality |
| `PreImageAnchor.geometric_anchor_dichotomy` | Sparse eligibility or a constructed fixed anchor representing all close finals |
| `PreImageAnchorSelected.pre_tau_geometric_anchor_dichotomy` | Exact natural1024/log20 and natural256/log18 specialization with actual overlap cap |
| `PreImageAnchorSelected.pre_tau_2325_anchor` | Focused 9300-fibre specialization, with no image-validity claim |

The runner checks the already-green research source/olean imports and the
committed Aspis cache closure against immutable main
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. It imports no untracked main K13
work. Lean is 4.32.0, Mathlib is
`81a5d257c8e410db227a6665ed08f64fea08e997`. Every build is serialized with
`-M7000` and a 7-GiB aggregate child-RSS guard; no cold or unchanged full
replay is used.

| Log | Exit | Wall seconds | Peak RSS bytes | Swap | Status |
|---|---:|---:|---:|---:|---|
| `pre-image-anchor-v1.log` | 1 | 26.84 | 5,433,327,616 | 0 | Explicit union arguments and named cardinality bounds needed |
| `pre-image-anchor-v2.log` | 0 | 9.49 | 5,596,381,184 | 0 | Both generic endpoints; standard axioms only |
| `pre-image-anchor-selected-v1.log` | 0 | 13.29 | 5,706,235,904 | 0 | Both selected endpoints, including B=2325; standard axioms only |

The two generic and two selected axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, new axiom, field enumeration,
cold dependency build, memory-cap increase or unchanged full replay was
used. Sources were frozen after their successful focused checks.

| Artifact | SHA-256 |
|---|---|
| `PreImageAnchor.lean` | `f80d73dde0b08459ffb9b33d55b56f9250e0b254f955466465e79b3d20f4b39e` |
| Generic olean | `ab339ce298d090b40597f450e67d2c9e6effb2d1464533562b7de0130ed93311` |
| `PreImageAnchorSelected.lean` | `3df68dde8f0b4518d633fdb7a50e0335495c12181703e64aafbea035c9c8b94b` |
| Selected olean | `13fcf9ecff685376b842525ba28f2fca8d3a6b63d578d18f8b8c23bd782b58d6` |

The selected replay also checks the 231-module committed Aspis source/olean
closure and all five required research imports before and after compilation.
It reuses `exactFinalEncoder_overlap_cap`,
`circleFoldLayer_circleLiftEncoder`, `exactInitialEncoder_eq_circleLift`,
and `canonical_one_fold_schedule_exact`; no new corresponding equality is
left as a source-shaped hypothesis in the selected endpoint. Actual Rust
and adversary-resource coupling remain separate from these mathematical
encoder identities.

```
bash docs/research/v8-no-work-100-20260907/experiments/run_pre_image_anchor.sh /absolute/NEW.log
bash docs/research/v8-no-work-100-20260907/experiments/run_pre_image_anchor.sh /absolute/NEW-selected.log PreImageAnchorSelected
```

The [joint composition](pre-anchor-joint-continuation.md) now uses the same
received word and this geometric Q, charging image/row/shifted-batch and
later-repair events once. That restricted endpoint leaves the farther-final
and image-valid component/payment recovery classes visible.
