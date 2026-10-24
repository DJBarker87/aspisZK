# Prover rewrite proof boundary

This adoption candidate now has a checked selected-sampler refinement (see
[Stage 3](PROVER-RW-20261023-STAGE3.md)). The security target
and the first conjunct of `ProverCommitDeployedFuel22.RustProverRefinement`
remain unestablished. This file records the actual source/model boundary;
it does not replace any required gate.

The actual per-attempt root `prover::prove_masked_with_attempt` was accepted
by Charon `extract-attempt-067` and Aeneas `aeneas-attempt-064`. Their retained
LLBC and embedded source hashes pin the input. Aeneas translation acceptance
establishes an extractable control representation. It does not establish
that the emitted Lean file typechecks or agrees with the mathematical prover.
`continuation/translation-attempt-064-audit.json` pins the generated files and
lists all 161 unbound template holes (12 types, 149 function/constant items).
No external template is installed as an axiom.

The source changed afterward to integrate the selected proof-account caller:
the retry callback is passed by value through a bounded recursive owner and
the ledger filename is built through an owned recursive string. Caller
translation receipts retain each failed source. The final caller translation passes in `extract-caller-005` and
`aeneas-caller-005` and supersedes the per-attempt input for source
attribution. Its audit enumerates 287 unbound template holes; these still
require exact external bindings and contracts.

The concrete proof obligations are:

| Boundary | Existing result eligible for reuse | Required new connection |
|---|---|---|
| Canonical fields, arithmetic and codecs | Pinned CT Kani receipts, typed native arithmetic/interpolation lemmas in parts 47–55 | Bind each selected external declaration, representation, precondition and result to its exact source body; audited reuse is local |
| Mask/context and private salt framing | Two source/body/harness-audited R2 contracts | Bind the rewritten control, state, guards and actual call order; no entropy distribution follows from framing |
| Retry, 64-byte factory and reservation | `RealR1_OuterOwner.outer_owner`, with explicit PrefixContract and BodyContract | Rebind the rewritten native control; discharge its prefix and body instances rather than assuming their desired equality |
| Semantic messages and openings | Model-side theorems and R3 rows 0–14 callee contracts | Prove full per-attempt status, proof/audit and retained state equality, including rejections and ordered oracle calls |
| Real experiment | `ProverCommitDeployedFuel22.RustProverRefinement` and the real-side endpoint | Instantiate the Rust experiment, witness/compiler/public mapping and observer transport; provide RunJoin on the fixed realBad event and realSeedQueries |
| Randomness and ledger environment | Existing named E1/E2 environment interfaces | Establish the concrete L1/L2 joint coupling and marginal laws required by the experiment; byte equality on fixed tapes is insufficient |

A per-attempt equality alone does not discharge conjunct 1: the conclusion
quantifies over adversaries and honest instances and joins complete ROM views
and observer decisions. Equal final proof bytes alone do not transfer an
adaptive oracle experiment. The old fixed bad events, query loss and security
bound must be preserved.

The continuation assigns env J 11200–11399. Attempts 11200–11211 use the
existing host launcher with the assigned range and task cap adapted in a
private copy. Usage is 12/100 Lean compiles, Kani remains 42/60.
`ProverRwSemanticSampler.sample_total_semChal` proves the selected normalized
sampler equals the existing semantic challenge component for every block,
with success and canonicality proved. This closes the retained sampler
wrapping/checked transport delta, not the full caller external binding or
per-attempt equation. The unmodified emitted sampler Funs fails its signed
shift-count API check; the explicit one-literal compatibility adaptation and
all failed/successful receipts are retained under `stage3/`.
