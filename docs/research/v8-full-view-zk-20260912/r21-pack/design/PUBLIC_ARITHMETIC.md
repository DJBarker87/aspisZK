# A different cost boundary: prove the public algebra instead of recomputing it

## Status

This is an architectural proposal, not an implemented auxiliary proof.
There is no claimed CU count, Fiat-Shamir theorem or source refinement for it.
The purpose is to make a falsifiable, bounded experiment rather than keep
projecting small arithmetic savings into an unsupported sub-1M claim.

## Why this direction

R20 E's instrumented trace has the following intervals:

* semantic total: 880,280 CU, including its retained basis;
* preparation: 249,648;
* query/tail arithmetic: 172,094;
* ordinary terminal: 785,531;
* G and final scalar: 170,590.

They sum to 2,258,143 out of 2,873,106. Merely subtracting them leaves 614,963.
That remainder is an OPTIMISTIC accounting subtraction, not a measured
rewritten native verifier or a lower bound. In particular the semantic,
preparation and query intervals include transcript hashes and sampling that
MUST remain native. Their cost must be put back, along with hints, error
handling and input processing. Measure that split before using the budget.
It nevertheless identifies the scale of the potential boundary.

The design goal is a **single shared auxiliary arithmetic proof** costing at
most 300k CU, including its complete public-input and wiring checks, with
an optimistic 615k remainder and 85k headroom BEFORE restoring those native
subcosts and adding glue. This is an engineering ceiling,
NOT a forecast. If the helper costs 700k, this design misses the target.

## Proposed division of responsibilities

Native code retains:

- canonical parsing and all length/domain/public-account checks;
- original SHA transcript framing, labels, challenges, rejection samplers,
  nonce/query selection and duplicate/draw-cap behavior;
- raw packed record validation and original-byte leaf hashing;
- both roots and paired Merkle authentication;
- public context/statement binding and final settlement authorization.

The helper proves exact arithmetic relations over the existing field:

- the semantic polynomial recurrence and terminal composition;
- public selector, Copy, Poseidon-extension and masking algebra;
- interpolant/ordinary-claim preparation;
- relation recurrences, final-vector folds and query-claim contraction;
- the ordinary, G and image contributions to the final scalar.

Start with ONE measured pilot, the ordinary terminal. Only enlarge the
circuit after verifying that it has a substantially cheaper complete proof
verifier. Eventually share input evaluation and intermediate values across
one combined circuit; dozens of independent little proofs may duplicate
more work than they save.

All inputs here are already public: proof coefficients, point/OOD claims,
opened records, sampled challenges, public statement and fixed layout data.
No witness, mask seed, C1 compiler or private prover trace is a helper input.
The intended helper is a layered arithmetic-circuit interactive proof in the
GKR family, then explicitly analysed under the project's existing shared
random-oracle model. This is NOT Groth16, a pairing wrapper, a trusted setup,
a trusted evaluator or an attestation by the prover.

## Essential interface and chronology

First extract a pure native function (or several pure functions) from the
ACTUAL assembled R20 stage. Do not define a new circuit and assume the source
implements it. Establish equality on arbitrary canonical inputs, including
invalid-proof image terms, then work toward universal refinement.

An illustrative interface is:

    compute_public_algebra(public_inputs) -> public_outputs
    prove_public_algebra(public_inputs, public_outputs) -> helper_bytes
    verify_public_algebra(public_inputs, public_outputs, helper_bytes) -> Result

The proof must certify output values, not only circuit well-formedness.
Every use of a claimed intermediate output is covered by a checked equation.
In particular, preparation outputs that enter an original transcript absorb
are supplied as hints and certified later; the original SHA engine still
absorbs their EXACT bytes in the original order. An incorrect hint must make
helper verification fail. No account may settle before that gate completes.

Bind the helper transcript to: a fixed circuit/version ID, the complete
original statement/proof instance or a canonical digest of it, all public
input encodings, all claimed output encodings, and the helper messages.
Fresh domain labels prevent encoding ambiguity; they are not a proof of
fresh independent oracle answers. Cached answers and prequeries still need
the real shared-oracle argument.

Implement arithmetic equality outputs or explicit residual checks. Never
assume an equality merely because it holds for an honest proof. Native
boolean/control decisions must either remain native or be range/boolean
constrained inside the actual certified computation.

## Acceptance and soundness composition

Let V be the existing native verifier. Let V* execute the proposed split,
with claimed arithmetic results h and auxiliary certificate pi.

The required deterministic property is:

    if h equals the native function's actual outputs,
    V*(original_input,h,pi) can accept only if V(original_input) accepts.

Together with soundness of the exact auxiliary relation, this gives the
usual union-bound decomposition: new false acceptance is contained in old
false acceptance OR acceptance of a false auxiliary arithmetic statement.
No independence of these events is required. It does require the source
refinement, all input bindings, and an actual noninteractive/helper soundness
argument. A root bound for one sumcheck polynomial is not that theorem.

Do not inherit an IID challenge law from GKR's interactive presentation.
Analyse the actual Fiat-Shamir conversion with query bounds, cache hits,
list/extraction effects where relevant, and the adversary's adaptivity.
Do not claim quantum random-oracle security from a classical analysis.
The original R19 pre-beta extraction and full soundness obligations remain;
an auxiliary proof cannot make an unsound underlying verifier sound.

## Why the privacy cost is potentially less disruptive

Require a canonical honest helper generator taking ONLY the original public
view and its own public-simulatable randomness. Then the added helper view
is an efficiently computable randomized post-processing of that view.
A simulator for the original view can run the same generator. In this
precise model, the helper creates no new private witness observation to
add to the C1/H1/G rank problem.

This is conditional on the original full-view privacy theorem and on the
stated generator interface. It is not a proof that current R19 is private.
A generator secretly using the private witness or arbitrary private proving
coins would invalidate this simple post-processing argument. Source stopping,
auxiliary failures and publication must also be included in the actual view.

## The implementation trap to avoid

A generic circuit verifier may evaluate wiring polynomials by scanning the
entire circuit, recreating the cost we attempted to remove. Count BOTH gate
verification and wiring-polynomial evaluation. The fixed 16/64 tensor blocks,
powers, permutations and selectors need a structure-aware wiring evaluator.
Include every public-input MLE/dot evaluation and fresh hash in the budget.

Pilot a concrete gate graph, not an abstract 'valid helper proof' parameter.
No universal provider premise, circuit-evaluation axiom or arbitrary asserted
rank is allowed as a substitute. An unsuccessful pilot is useful evidence.

## Explicit experiment order

1. Freeze R20 clean B and both retained genuine fixtures. Add more independently
   generated fixtures and malformed cases; two honest worlds are insufficient
   for a complete resource profile.
2. Extract the exact ordinary scalar evaluation, retaining T163, all four
   fold challenges, arbitrary final values, pivot/inactive/image corrections.
3. Produce its explicit regular layered circuit and an independent evaluator.
4. Implement prover AND verifier for that circuit. Tamper with every output,
   layer message and input binding. Measure full SBF helper verification.
5. If it is not convincingly cheaper than 785k, do not expand the architecture.
6. Compose one circuit for the other expensive arithmetic with shared public
   inputs. Keep hashing/authentication native. Test the complete 1M gate.
7. In parallel, close source/refinement and real shared-oracle security. Passing
   the resource gate never substitutes for either security obligation.

## Sources for the general construction (not Aspis performance evidence)

Goldwasser, Kalai, Rothblum, "Delegating Computation: Interactive Proofs for
Muggles" (2008), author publication page:
https://www.microsoft.com/en-us/research/publication/delegating-computation-interactive-proofs-muggles/

Thaler, "Time-Optimal Interactive Proofs for Circuit Evaluation" (2013),
author page and paper:
https://people.cs.georgetown.edu/jthaler/TimeOptimalIPs.html
https://arxiv.org/abs/1304.3812

These establish the general delegated-computation direction and importance
of regular wiring, NOT a claim that this particular circuit fits Solana.
