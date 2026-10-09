# Actual monic OOD branch into the V7 Hensel interface

Status: `MonicOODBranch.lean` is green; all 14 audited declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`. This is a deterministic
branch-construction result, not a completed higher-Y count or soundness theorem.

## Checked endpoint

For the literal fixed answer polynomial `A(Z)`, define `branch A = Y-A(Z)`.
The leaf derives its monicity, degree one, nonzero leading coefficient,
irreducibility over the actual V7 field `K(Z)`, and empty local pole set.
Its adjoined root is proved equal to the embedded `A`, not supplied as a
correspondence premise. The actual equality `U(x)=A(gamma)` supplies its local
specialization equation.

For fixed `F`, `x`, and `A`, the two hypotheses

- `FactorCoherence.pointSubstitution x A F = 0`;
- `FactorCoherence.derivativeCurve F x A != 0`

construct the exact borrowed `liftedGlobalFactor F x (branch A)` power-series
root with the required adjoined-root constant coefficient. The leaf also
derives `regularizedHenselDerivative F x (branch A) != 0`. The latter maps to
the embedded literal derivative curve because the leading coefficient is one.

No full-resultant certificate or membership in a canonical normalized local
factor registry is assumed. Other branches at the same point may be singular.
The root and regular denominator are fixed before every gamma and later
candidate; no adaptive final is moved to an earlier transcript prefix.

## V7 reuse and downstream boundary

Borrowed source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

- `V7ExactCorrelatedAgreementPowerSeriesLift` supplies the literal shifted-X
  map and its two constant-coefficient commuting identities. Source SHA-256
  `892af45824af2fab92db4e63454d82d25ae6231ac4b9ef5f6e7644fab8120db1`;
  cached olean `7f133aeee3d277bf90863ec07dc9a8ad84d8c494f456e8f3212db448dfd30d0b`.
- `V7ExactCorrelatedAgreementRegularHensel` supplies the exact regularized
  denominator and its function-field image. Source
  `411aa5c9e5098739238679ae52b073697cddd85097fbb0e14bc56fa9d94bea34`;
  cached olean `dae92645b2f1b13886622c266b97e1077c63cfc1563c8cc0de4a2baa84fd173d`.
- `V7ExactCorrelatedAgreementHensel.exists_powerSeries_root_of_simple_constant_root`
  constructs the root from the two derived constant-coefficient conditions.
  Its source hash is
  `0762122b085cddcc6ec1ac4bb573edceb15d8789565310a57298c6d5a052cbde`.

The two direct imported pairs and their pinned closure were already in the
NUC overlay; no missing-dependency export or cold build was performed. Native
Mathlib remains a pinned-package cache boundary, not a replayed package build.

The next consumer is
`V7ExactCorrelatedAgreementFixedBranchCurve.exists_ambient_curve_of_fixed_branch`.
With `k=1024`, curve degree `28`, local degree `1`, local weight bound `28`,
and actual factor weight `W`, its exact branch budget simplifies to
`B = 28 + 2047*(W-28)`. The actual covered-original interface retains at least
`38230` symbols on a domain of `1048576` points, so its strict incidence
condition is `|G|*37206 > 1048576*B`.

This leaf does not prove the remaining actual agreement/degree adapter, the
coefficient-weight specialization, or the ambient-to-polynomial-curve bridge.
The generic `ReleasedLift.exists_released_components_of_ambient_curve` does
preserve the real encoder image from 29 actual selected messages; ambient
degree alone must not be substituted for that interface. The separate
`HigherYCurveObstruction` bounds roots once such a polynomial curve exists.

For orientation only, completing those interfaces would give a regular-row
per-factor count of at most
`(W-28) + floor(1048576*(28+2047*(W-28))/37206)`.
The first term charges that fixed row's nonzero derivative polynomial.
Using the additive retained-factor weight budget `sum W <= 117077`, the
same single-factor maximum is `6752740499`, not this number times 37 or 111.
This scalar arithmetic is a design calculation, not a newly checked Lean
probability endpoint. Dividing this numerator alone by a roughly 124-bit
gamma domain would give only about 91.35 bits. No 100-bit claim follows.

Both-singular OOD identities remain outside this regular-row result.
Irreducibility is not absolute irreducibility, and a simple specialized
linear Y factor need not make a resultant vanish. Acceptance-to-coverage,
outside-family events, early-C1 own support, actual query probability,
later repairs, and checked payment extraction remain separate interfaces.

## Focused execution evidence

Working source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Inherited runner/overlay origin: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
These revisions have different roles; the inherited origin does not claim
the new source existed at that revision.

Remote scope: `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`.
Connection: Tailscale `dombarker@100.108.41.90`, with `HostKeyAlias=nuc.local`
only for the previously verified SSH host key. The live preflight showed
only `init.scope`, with 43 GiB available. No competing formal build was
launched. Each attempt used `run_higher_y_nuc.sh TASK MonicOODBranch TAG`:
Lean 4.32.0, `-j1 -M9500`, memory high 8 GiB, maximum 10 GiB, swap maximum zero,
CPU quota 200%. Runner SHA-256:
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

| Attempt | Exit | Wall | Peak RSS (KiB) | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| `monic-ood-branch-nuc-v1` | 1 | 4.58 s | 6808160 | 0 | Two local normalization failures; retained diagnostic only |
| `monic-ood-branch-nuc-v2` | 0 | 4.66 s | 6841612 | 0 | 14 standard-only audits, 891-entry provenance unchanged |

V1 unfolded the dependent branch type while simplifying its root equation,
and did not normalize an empty multiset before applying `toFinset_zero`.
V2 isolated the evaluated branch expression with a typed `change` and named
rewrites, and inserted `Multiset.empty_eq_zero`. No statement, mathematical
premise, resource limit, or dependency changed. V1's downstream `sorryAx`
diagnostics are not green evidence; the final audits contain none.

All attempt source snapshots, manifests, and logs are retained locally under
`experiments/monic-ood-branch-nuc-v{1,2}-*` and the matching `.log` paths.
The green output is `experiments/MonicOODBranch.olean`.

Final SHA-256 values:

- Source and v2 source snapshot:
  `09af9553348aa356033e2c647af8180d1fac5f2009a910cd8462efcaed9026b7`.
- Olean: `15d7568dec06a9ad3e3615f7a8c617dc14a50f15d4a539f14abb36cc9160fc9c`.
- V2 log: `6a75ce060f288a097278c32eed8c60331a2ea8adb5ad8b2a2b2b0643e3b844b8`.
- V2 manifest: `2715fc5a3410aac8c431eff8c45ecebad7036b0681577c6d7a11b6c0eabf1026`.
- V1 source: `68d1b585bab809c55036924067947fddb953ae5c2dc3868102dff6b1ea78d8f9`.
- V1 log: `0e5260f4e81606f2c7e47895aa18ab6497e50b58e746a1cc9bc3e32b4989097c`.

No Rust, default protocol, production source, or frozen proof leaf changed.
`NestedCircleSlotAlignment.lean` remains preserved but uncompiled after the
user's higher-Y reprioritization; it is not part of this evidence.
