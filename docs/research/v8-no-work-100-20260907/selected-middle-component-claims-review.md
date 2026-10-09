# Same-tuple ordinary component claims — focused Lean result

Status: v1 reached the proof and failed only at the two finite-family membership applications (`familyBad_subset`, `family_claims_exact`). V2 applies declaration-local recursion depth 400 to exactly those two declarations and is now **kernel-green**. All nine printed declarations are free of `sorryAx` and new axioms.

V2: [SelectedMiddleComponentClaimsV2.lean](experiments/SelectedMiddleComponentClaimsV2.lean), SHA256 `ce588a03c2bd22f745faac7344e4f7589f2d4c95c79c6df29638486e4a455ff3`.
The attempted [v1 source](experiments/SelectedMiddleComponentClaims.lean) remains unchanged, SHA256 `ffeba8efc576b9fd08ded921b468c60f1535fd604aa34c8a89d7a690a5579a88`.
Working parent: `7c8e18488f1337b1ff247908a1a8e86325ec29bb`.

## Exact endpoint

Fix a tuple `p : Fin29 → Fin1024 → K`, ordinary weights `w`, and87 claimed component values `a` before gamma. For row `r : Fin3`, use the existing literal polynomial

`E_r(Z) = ∑ lane, (a r lane − covector (w r.succ) (p lane)) Z^lane`.

Every `E_r` has degree at most28. `chosenError` selects one nonzero `E_r` if any exists, otherwise zero. This choice depends only on `p,w,a`, not gamma, the inactive scalar, Q, kappa, tau, alpha, queries or their acceptance. `badGammas` is empty for a zero chosen polynomial and otherwise its roots within the original gamma domain. The draft proves its cardinality is at most28; it does not union three separate28-root sets.

`represented_rows_force_root` consumes the actual two premises:

1. `d.original Q = ClaimTransport.batch d.gamma p`, for the SAME Q and p;
2. `(ComponentRows.rows d quarter w a inactive Q).errors = 0`.

`Data.original` and `ComponentRows.original` are literally the same reconstruction-plus-interpolant expression. The existing `ComponentRows.recovered_point_error` therefore forces the chosen error polynomial to vanish at `d.gamma`. Outside `badGammas`, its zero case gives all87 equalities by `ClaimTransport.component_error_coeff`.

For any fixed family with `family.card≤1`, `familyBad` unions these sets over the family and still has cardinality at most28. `family_claims_exact` is uniform over all subsequently selected family members, data, inactive scalars and quotients. It consumes the family/cap already supplied by `SelectedMiddleImageRecovery.exists_recovery`; no new family construction, same-support hypothesis or `earlyC1=some` appears. Image/own-support conditions are not repeated once that theorem has supplied the actual representation.

## Timing and scope

The three component functionals and claimed values must be fixed before gamma. The concrete `Data`/`Rows` record and inactive scalar may depend on gamma: neither enters the error polynomial. The inactive scalar must still precede kappa in the source game, but this deterministic lemma does not itself establish that challenge law. If “row may depend on gamma” means that the three functionals themselves change, the28-degree argument would not apply; only the reconstructed ordinary-row record may vary here.

Zero of the complete ordinary error vector is an explicit premise. A single sampled-kappa discrepancy equal to zero does not establish it. Its source justification is the represented quotient's ordinary-row-correct branch from the existing relation partition; scalar repair/collision alternatives remain upstream. Likewise, selecting p from a post-gamma family would invalidate the intended pre-gamma cardinality application even though each pointwise algebraic theorem remains true.

The result concerns87 ordinary claims, not the separate58 OOD component answers, semantic row vanishing, copy aliases, checkpoint authority or payment validity. It supplies the missing SAME-p point-claim link identified in the recovery audit without29-node forking or retrospective interpolation. Turning the cardinality into an actual probability still needs the correct gamma law and causal family fixing.

## Reuse and next check

Direct imports are only `ComponentRows` and `QuotientOriginalCore`. The proof reuses `ClaimTransport.component_error_degree`, `component_error_coeff`, the literal source `ComponentRows.recovered_point_error`, and the existing finite polynomial-root/union bounds. It does not import or edit the pending recovery assembly. V2 changes only the two failed finite-family membership declarations to declaration-local depth400 (including their linter); all core algebra and other declarations retain depth200, and heartbeat200000 is unchanged. Ordinary comments precede the immediately scoped declarations. No theorem statement or proof body changes, concrete field enumeration or recurrence evaluation are introduced.

The focused NUC command was:

```text
bash ./run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SelectedMiddleComponentClaimsV2 \
  selected-middle-component-claims-v2-nuc-v1
```

It ran Lean 4.32.0 with `-j1 -M9500` in a systemd scope capped at
`MemoryHigh=8 GiB`, `MemoryMax=10 GiB`, `MemorySwapMax=0` and `CPUQuota=200%`.
Exit status was 0; wall time was 5.95 s, peak RSS 6,700,200 KiB and swap 0.
The inherited research pin was
`289d7356c78a4cd493fe61a54f9548f2a0c11298`; overlay provenance passed for
1,067 inputs and was unchanged after the run. Evidence:

- [manifest](experiments/selected-middle-component-claims-v2-nuc-v1-manifest.json)
- [frozen source](experiments/selected-middle-component-claims-v2-nuc-v1-source.txt)
- [log and axiom audit](experiments/selected-middle-component-claims-v2-nuc-v1.log)

This closes the deterministic same-tuple claim-binding seam only. It does
not establish the upstream ordinary-row-zero event, gamma freshness, payment
semantics, authentication, or the Fiat--Shamir lift.

## Optional post-recovery claim-binding charge

This is a separate conditional extension, not part of the residual-recovery
theorem or its recorded arithmetic. Let `T` be the exact `total` in the
[residual-recovery record](residual-recovery-probability.json), SHA256
`212dd471660abd9404bde29832e5cb677f6edcd8c505531c4589bcd9eb983f16`.
For its recorded domain
`g = |Gamma| = (2147483647)^4 - 1 = 21267647892944572736998860269687930880`,
the optional extended bound is exactly

`T_claims = T + 28/g = T + 1/759558853319449026321387866774568960`.

The middle exceptional numerator becomes `104 + 28 = 132`, and the combined
gamma-root numerator becomes `117049 + 132 = 117181`. The product-pair bound,
LOW integrated query/alpha bound, and once-only suffix repairs are unchanged.
This is an additive union bound: no independence, disjointness, successful-retry
conditioning, or replacement of the original gamma denominator is used.

| Conditional arithmetic line | Probability upper bound (approx.) | Negative log2 (approx.) | Share of the `2^-100` budget |
| --- | ---: | ---: | ---: |
| Recorded residual recovery `T` | `4.930816525590405970e-32` | `103.999872464867748578` | `6.250552528279950786%` |
| Optional same-tuple claims `28/g` only | `1.316553675373234324e-36` | `119.192645075255166972` | `0.000166893005681956%` |
| Residual recovery plus optional claims | `4.930948180957943293e-32` | `103.999833944673540806` | `6.250719421285632743%` |

The incremental bit cost is approximately `0.000038520194207771`; the extended
bound remains strictly between `2^-104` and `2^-103`, and below `2^-100`.
These are exact rational bounds with decimal logarithms, not an unconditional
security claim or a rounded-up 104-bit result.

Applying this extension requires the recovered SAME tuple to belong to the
fixed family of cardinality at most one, with its component functionals and
claims fixed before gamma, the stated original-domain gamma law, and the actual
ordinary-row error vector equal to zero. The last premise is upstream: a single
kappa check is insufficient. If ordinary-row correctness has not already been
obtained outside charged relation-repair events, those events still need their
own justified bound; this `28/g` term does not provide it. No payment-witness or
authentication conclusion is added.

Tiny read-only reproduction (no field enumeration or Lean run):

```sh
python3 - <<'PY'
from pathlib import Path
from fractions import Fraction
from decimal import Decimal, localcontext
import hashlib, json
p = Path('docs/research/v8-no-work-100-20260907/residual-recovery-probability.json')
assert hashlib.sha256(p.read_bytes()).hexdigest() == '212dd471660abd9404bde29832e5cb677f6edcd8c505531c4589bcd9eb983f16'
r = json.loads(p.read_text())
t = Fraction(int(r['total']['numerator']), int(r['total']['denominator']))
g = int(r['parameters']['gamma_cardinality'])
assert g == 2147483647**4 - 1
e = Fraction(28, g)
assert e == Fraction(1, 759558853319449026321387866774568960)
assert Fraction(1, 2**104) < t < t + e < Fraction(1, 2**103) < Fraction(1, 2**100)
with localcontext() as c:
    c.prec = 80
    for label, value in [('residual', t), ('claims-only', e), ('extended', t + e)]:
        d = Decimal(value.numerator) / Decimal(value.denominator)
        print(label, format(d, '.24E'), format(-d.ln()/Decimal(2).ln(), '.18f'),
              format(d * Decimal(2**100) * 100, '.18f') + '%')
PY
```

Result: the rational addition, original seven-term sum, and strict dyadic
comparisons passed. The residual-recovery Python/JSON were not modified.
