# Quadratic cover connected to causal accepted mass

Source parent: `51692ed712ecb646b51e15e4b8e93e149a6b4014`.

Two new Lean leaves are checked. `SelectedQuadraticReduction` preserves
the existing same-candidate factor classification and refines its
degree-at-least-two branch to the quadratic OOD/gamma exceptions or a
degree-at-least-three factor. The old linear OOD polynomial, linear sparse
gamma set and small message-tuple family are retained with their exact
scope. See its separate focused review.

`CausalQuadraticReduction` connects the selected quadratic cover to the
same compact relation/query suffix model used by `CausalFactorReduction`.
It constructs a nonzero E of degree at most 114687 from C1/C2 before
quantification over the OOD data and all later strategies. Its bound is:

    quadratic accepted mass
      <= indicator[both OOD points root E] + 936616 / |Gamma|.

Gamma is the model's nonempty finite uniform challenge set. This is not
a statement that the deployed Fiat–Shamir sampler supplies that law.
The total reduction is:

    total compact-suffix acceptance
      <= existing missing-good ceiling
       + 117077 / |Gamma|
       + indicator[both OOD points root E]
       + 936616 / |Gamma|
       + remaining accepted factor mass.

The existing ceiling, including relation/query repairs, and the earlier
factor-cover exception are each used once. No term is imported from the
historical 396430 inventory. The two gamma numerators apply to different
stages in this decomposition; the proof does not assume independence.

## Total accounting within the inspected ideal suffix

| Class | Definition/treatment |
| --- | --- |
| Missing good quotient | Existing `CausalCoveredRecovery` ceiling, unchanged |
| Good but no factor prefix | Existing 117077 polynomial exception, unchanged |
| Quadratic prefix | A factor prefix and a same-final, image/row-good Q with a quadratic factor root; new charged class |
| Remaining factor prefix | `factorPrefix AND NOT quadraticPrefix`, its full accepted suffix mass retained |

The last two classes partition factor mass exactly. The remaining mass
is NOT assumed to be extraction failure: it can include valid small-tuple
representations, higher-degree factors and other unresolved recovery
cases. Conversely, no provider success, decoder existence or payment
validity is inferred from a factor classification.

In the quadratic class, Q may depend on gamma, kappa, tau and alpha;
the full strategy still fixes the actual final before queries and rho.
The proof bounds the actual causal continuation by one on exceptional
gamma values. Outside the fixed gamma set and OOD obstruction it derives
that the quadratic prefix is absent, so its accepted mass is zero. It
does not freeze the candidate before its true selection time.

## OOD and source boundary remains explicit

The two OOD points are NOT averaged in this leaf. The ideal suffix
`Execution` stores them as pre-gamma data. The theorem chooses E before
all executions with the same C1/C2, which permits a later sequential OOD
lift without retrospectively choosing E.

The actual research prefix samples point0, absorbs its component vector,
then samples a distinct point1 with bounded retries and absorbs its
vector before nonce/gamma. The inspected V7 ordinary-scalar pair law
concerns different messages and cannot be used as that circle sampler's
source theorem. The separate sampler audit identifies the next exact
adapter. Until then the OOD indicator remains symbolic, not a numerical
probability or an implicit independent-pair assumption.

This is an ideal source-shaped compact-suffix theorem. It does not
complete authenticated-oracle access, real replay/fuel accounting,
payment extraction, full Rust refinement, primitive assumptions,
Fiat–Shamir resource bounds or full-view privacy. The full goal remains
open. The proof body is unchanged at the 40,282-byte maximum, and no
work/grinding security credit or new verifier operations are introduced.

## Focused evidence

`CausalQuadraticReduction` v1 passed: exit0, 3.27s, peakRSS6,888,240KiB,
zero swaps, four standard-only axiom audits. No failed attempt.
Command: `bash run_higher_y_nuc.sh <scope> CausalQuadraticReduction causal-quadratic-reduction-nuc-v1`.
Same NUC/Tailscale scope, Lean `-j1 -M9500`, MemoryHigh8GiB,
MemoryMax10GiB, MemorySwapMax0, CPUQuota200%. The inherited runner/cache
pin remains289d7356 independently of the new source parent. Exact
imports passed provenance validation before and after the run.

Source SHA256:
`40e1e90ecf31dee7564895a02a624ceee78f892e19d2c5fdb5e2a63b880e0dfc`.
Olean SHA256:
`4b65e124539cef9ab891fbb31cd0af0bf0e05600a24fe1deeb7330c2d6e10d76`.
The classification leaf passed separately (two audits). Neither is a
prover, SBF, complete-transaction CU or executable-extractor measurement.

Next: prove the literal sequential distinct-circle sampler adapter, then
compose its OOD charge with this fixed-prefix reduction. Keep the
degree-at-least-three and tuple-to-witness branches explicit throughout.
