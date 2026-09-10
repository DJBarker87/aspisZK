# Polynomial-valued interpolation for a restricted linear-factor class

Research parent: `6f1ebbe55fcc6fd008071329d5270aae0521cf9a`.

## Exact mathematical scope

Fix an injective map `phi : K[X] → L` into a field and a polynomial
`R ∈ L[Z]` of degree at most `c`. At `c+1` distinct scalar nodes, suppose
`R(gamma) = phi(U_gamma)` for polynomial messages `U_gamma` of X-degree at
most `D`. The checked [PolynomialValueInterpolation](experiments/PolynomialValueInterpolation.lean)
constructs

`p_j = sum_gamma coeff_j(LagrangeBasis_gamma) • U_gamma`.

Every coefficient of `R` is the image of this explicit polynomial `p_j`.
Consequently every later polynomial value of `R`, including an adaptively
chosen one, equals `sum_j gamma^j • p_j`. Each `p_j` has X-degree at most
`D` and belongs to any `K`-submodule containing all the node messages.
This last property preserves an actual linear code subspace; the weaker
degree bound alone must not be mistaken for circle-code membership.

The checked [LinearFactorInterpolation](experiments/LinearFactorInterpolation.lean)
fixes `A,B ∈ K[X][Z]`
and assumes an actual polynomial-in-Z root over `K(X)`:

`map(A) * R + map(B) = 0`, with `degree_Z R ≤ 28`.

For every regular specialization `A(gamma) != 0`, the literal equation
`A(gamma)*U+B(gamma)=0` derives the required value equality by cancellation.
Define good gamma geometrically by existence of such a polynomial `U` in
the chosen code submodule, of X-degree at most 1024. The proved dichotomy
is at most 28 good gamma in the fixed finite challenge set, or a constructed
29-component submodule-valued curve identifying every regular polynomial
root. Nodes are chosen from the geometric good set, not from a provider's
actual postchallenge answers. No component tuple is supplied as a premise.

The root-polynomial assumption is a genuine restriction on retained linear
factors, not a consequence established here of two OOD identities. In
particular, arbitrary rational functions of gamma remain outside this
class. Specializations with `A(gamma)=0` are explicitly excluded in this
leaf. The subsequent [selected source bridge](selected-grs-submodule-review.md)
uses the checked primitive/prime-factor argument to remove that regularity
premise for actual prime linear factors and instantiates the submodule
with the literal original-code image. There is no efficient factorization,
list extraction, source replay,
authentication, canonical decoding, payment validity, or probability claim.

## V7 reuse and proof boundary

The coefficientwise Lagrange construction reuses the method of
`V7ExactCorrelatedAgreementReleasedLift.releasedInterpolationComponents`
and its node-identification theorem. That V7 source has SHA-256
`83581c24ea8dd1ba7b36aa2d90833d68901111c20b9787a0416bd68cc3bd9612`.
The new core imports only cached `Mathlib.LinearAlgebra.Lagrange`; it does
not import the large V7 Hensel tower or assume its ambient-to-released-code
correspondence. The genuinely new step is coefficient descent from the
fixed extension-field polynomial, which identifies all later values,
not just the interpolation nodes.

The earlier rational-helper example
`R(Z)=Z^26*(Z-b)/(X-a)` belongs to this restricted class. The absence of a
global polynomial coefficient curve is consistent with the sparse branch;
it is not a counterexample to interpolation. A separate exact specialization
control is owned by the root agent.

## Focused evidence

All checks use the dedicated NUC, not the laptop. Workspace:
`/home/dombarker/project-offloads/aspis-linear-factor.8SUGGL`.
The pinned runner is [run_linear_factor_nuc.sh](experiments/run_linear_factor_nuc.sh),
SHA-256 `ff4db59289e0f873ab2892ebf6f8dcf294966ec42a457f3cff0c09bec01093bb`.
It enforces MemoryHigh 8 GiB, MemoryMax 10 GiB, zero swap allowance,
CPU 200%, and `lean -j1 -M9500`. No resource or elaboration limits were
raised for this task. Each attempt retains its exact source snapshot,
manifest, log, and successful output where applicable.

| Target / attempt | Exit | Wall | Peak RSS (KiB) | Swap | Status |
| --- | ---: | ---: | ---: | ---: | --- |
| PolynomialValueInterpolation v1 | 1 | 1.51 s | 2,273,416 | 0 | Diagnostic only |
| PolynomialValueInterpolation v2 | 0 | 1.35 s | 2,286,360 | 0 | Six standard-only axiom audits |
| LinearFactorInterpolation v1 | 0 | 1.27 s | 2,283,752 | 0 | Four standard-only axiom audits |

V1 failed because theorem headers requested `DecidableEq K` before the
proof-local `classical` tactic, followed by two local proof-interface
issues. V2 makes that generic parameter explicit, unfolds only the
component sum for submodule closure, and specifies the finite-sum function
in its symbolic `Fin`/range transport. No large finite field or recurrence
was enumerated. V1 source and log remain diagnostic evidence, not a green
release result.

Core v2 source SHA-256:
`51c6deee77dc55212587154c25480aa1e691809d3582fafb207f2edf588a215a`.
Core v2 olean SHA-256:
`8d0584f84c4c5b11e88c556f3727d195dae46550058950e1d2db7a6b2fe4f2d8`.
The source, log, and manifest use the
`experiments/polynomial-value-interpolation-nuc-v2` prefix.
Dependent v1 source SHA-256:
`e82ceb9bd0c463c0fa00ef7d3d6c0a16020727d47c6cb96b9182eb72d43e8179`.
Dependent v1 olean SHA-256:
`51cf2ac2cd293f050baeb2a48f9cc61b705bf3cdd0d3c23aabf3a3afc98c81f3`.
Its source, log, and manifest use the
`experiments/linear-factor-interpolation-nuc-v1` prefix. A harmless unused
section-variable warning remains in `map_eval_constant`; the successful
source is frozen rather than replayed for a cosmetic change.
Audited dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
The per-run provenance pins borrowed sources to
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5` and Mathlib to
`81a5d257c8e410db227a6665ed08f64fea08e997`; cached packages are not claimed
to have been rebuilt in this turn.
