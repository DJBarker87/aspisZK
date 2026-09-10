# Selected discriminant X-degree and characteristic guard

[QuadraticSelectedDegree.lean](experiments/QuadraticSelectedDegree.lean) is
green with four standard-only axiom audits. Source parent:
`be7a1731bd4d71de50fa39767a53523bf0bc9ff0`; reused NUC-scope parent:
`289d7356c78a4cd493fe61a54f9548f2a0c11298`; borrowed V7 source pin:
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

For the actual source discriminant
`D(F) = swap(F.coeff 1)^2 - 4*swap(F.coeff 2)*swap(F.coeff 0)`, the new
generic theorem proves `deg_X D(F) <= 2*deg_X F`. The coefficient bound is
the pinned V7 `reorderFactorCoefficients_coeff_natDegree_le`, instantiated
at the three literal indices. Polynomial product, square and subtraction
degree inequalities finish the argument. Zero coefficients and cancellation
are allowed; neither irreducibility nor degree Y equal to two is needed for
this degree inequality itself.

The selected endpoint assumes only membership in
`curvePrimeFactors (SelectedFactorCoherence.parent c1 c2)`. It derives the
parent's nonzeroness from `fixedInterpolant_nonzero`, consumes V7
`curvePrimeFactor_xNatDegree_le`, and uses the already-green
`SelectedMonicCover.parent_x_degree`. Consequently every such factor has
`deg_X D(F) <= 229374 < 2147483647`. The source-dichotomy characteristic
*degree premise* no longer needs to be supplied by a caller.

The four audited endpoints are `coefficient_x_degree_le`,
`discriminant_x_degree_le`, `selected_discriminant_x_degree_le`, and
`selected_discriminant_lt_characteristic`. Each depends only on `propext`,
`Classical.choice` and `Quot.sound`. The final source has no new axiom or
`sorry`; failed diagnostic audits below are not retained theorem evidence.

## Focused evidence

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps | Scope |
|---|---:|---:|---:|---:|---|
| v1 | 1 | 2.81 | 6830292 | 0 | Swap coercion and invalid local-abbreviation syntax; downstream selected elaboration failed |
| v2 | 1 | 2.84 | 6828460 | 0 | Both generic lemmas checked; selected membership specialization reached depth 200 |
| v3 | 1 | 2.80 | 6828576 | 0 | Family opacity fixed membership; arithmetic saw two differently named aliases as separate atoms |
| v4 | 0 | 3.37 | 6861876 | 0 | All four audits standard-only; complete postflight passed |

No resource cap was raised. The replacement used named symbolic facts:
explicit ring-equivalence coercion simplification, a valid private type
abbreviation, local opacity of `curvePrimeFactors`, and explicit normalization
of the private K/`SelectedReceivedOracle.K` aliases before Nat arithmetic.
No chosen factorization, concrete field or finite universe was enumerated.
All changes were confined to this new file; no frozen dependency was edited.

Every attempt's exact source snapshot, log and per-run manifest is retained
as `experiments/quadratic-selected-degree-nuc-vN-source.txt`, `.log`, and
`-manifest.json`, for N=1,2,3,4. The successful compiled output is
`experiments/QuadraticSelectedDegree.olean`.

Final source/snapshot SHA-256:
`8b276ac6b4623ab8eab69cfc9f0dad8b5b7021ae3cf4375cb21b6818970a4b22`.
Olean SHA-256:
`2a9d047daaf9cef51f6520d784de586ef1a067d463964f574b9d74c6840f33b1`.
Successful log SHA-256:
`f6ce6aa8c54ab3dd26775792b7ffd562e01cd4adc6c552108409d2edddb96835`.
Successful manifest SHA-256:
`3a3fc3a21b10fdf898d83dc984eb29e02152017d818c70c656d92886e0f097f9`.

Historical successful command (not an unchanged replay instruction):

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes \
  -o HostKeyAlias=nuc.local dombarker@100.108.41.90 \
  'bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  QuadraticSelectedDegree quadratic-selected-degree-nuc-v4'
```

The prelaunch reservation check found no running user build scope and
43 GiB available. Every run used Lean 4.32.0, `-j1 -M9500`, MemoryHigh 8GiB,
MemoryMax 10GiB, MemorySwapMax 0 and CPUQuota 200%. The green run verified
839 overlay artifacts before and after, with provenance unchanged.
Native package compilation remains a pinned-revision cache boundary.
Tailscale carried the network connection; `nuc.local` was only the verified
host-key alias. The sole compiler slot was explicitly released after v4
terminal postflight. No concurrent V7 process or state was changed.

## What this does not infer

The family is fixed after C2 and before OOD, not before lambda/chi: C2 may
depend on those earlier challenges. This leaf is a degree guard, not a proof
of actual acceptance, root existence, factor Y-degree two, a challenge law,
or efficient extraction. The separate QM31 `CharP` instance can be derived
from its faithful M31 algebra map; this file proves the numeric strict bound,
not a new characteristic instance. The full batching weight remains 28, and
the degree-two helper curve is not substituted for it. No production,
default, transcript, proof-size, CU, prover or grinding change was made.
