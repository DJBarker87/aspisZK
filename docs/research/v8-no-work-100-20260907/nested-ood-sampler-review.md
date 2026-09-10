# Nested OOD sampler continuation

Source parent: `d0e3196848b89de8ddf1a85fcc0a6e55bf8fdc95`.

This continuation closes two previously separate ideal/source prerequisites,
but does not yet connect them by an oracle-measure theorem.

## Checked ideal mass

`NestedCircleMass` proves the exact unconditional mass of each fixed ordered
distinct admissible QM31 parameter pair under the source-shaped three-attempt
circle sampler and three-attempt distinct wrapper.  Ordinary decode failure,
inner exhaustion, and outer exhaustion contribute zero rather than being
conditioned away.  The state between the two point samples may depend on the
first answer.

`RetryMassArithmetic` and `RootSetPairMass` then prove that a fixed admissible
target set of size `m` receives total ordered-pair mass at most

    m(m-1)/(N(N-1)),  N=P^4-P^2.

For the intended same-`E` root set with `m<=114687`, this term is at most
approximately `2^-214.3853278887`.  The exact rational is recorded in
`nested-ood-mass-ledger.json`.  No success conditioning, independent-label
premise, or grinding/work contribution occurs.

## Checked literal routing

`NestedCircleSourceRefinement` proves the ordinary decoder's exact first-hit
block cut and unread-suffix locality. `NestedCircleStatusRefinement` proves
the detailed need-more/hard-failure/accepted seams, including that accepted
one-block continuation leaves no unread whole block and that four blocks are
decisive. `NestedCircleRunRefinement` uses those facts to prove whole finite-
tape accepted-result equality between the literal first-circle3 followed by
distinct3(circle3) source call and the chronological controller.  It also
proves that every controller abort gives literal source `none`.

The run theorem deliberately does not assert the false converse on a short
tape: source `none` can mean that the controller is still waiting. Halted
updates are inert padding, not additional source consumption.

## Missing connection

Deterministic equality on every tape does not establish that the actual hash
oracle supplies the history-uniform coin law assumed by `NestedCircleMass`.
The next decisive theorem is a measure-preserving coupling from the actual
fresh, domain-separated byte callbacks (including the answer-dependent state
between OOD points) to the finite-tape controller. It must retain repeated
inputs, prior oracle queries, aborts, and cached/advance mismatch branches.

Only after that coupling is checked may the fixed set be instantiated with
the admissible roots of the same pre-OOD polynomial `E` from
`CausalQuadraticReduction`, using the actual parameter/point inverse and
degree bound. The result can then replace the explicit OOD indicator in the
causal reduction. `residualProbability` remains a real accepted class; it is
not silently renamed degree-three recovery or discarded.

The proof body remains 40,282 bytes. These proofs change neither the wire nor
verifier CU. The global raw-security theorem, payment-witness extractor,
resource-bounded Fiat--Shamir lift, adaptive full-view ZK, and matched complete
transaction CU parity remain open.

## Evidence map

Each focused module has its exact NUC attempts, source snapshots, manifests,
logs, green o output and axiom audit report beside it. All jobs used Lean 4.32,
`-j1 -M9500`, an 8 GiB memory-high / 10 GiB memory-max cgroup, zero swap, and
the Tailscale route to the NUC. The individual reviews record hashes, elapsed
time and peak RSS. No package-wide or unchanged full replay was run.
