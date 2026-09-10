# Nested circle retry mass

Source parent: `d0e3196848b89de8ddf1a85fcc0a6e55bf8fdc95`.
Status: **checked**. `NestedCircleMass` v2 passed its focused NUC check with
eleven standard-only axiom audits. The exact scope remains the finite-coin
history-indexed experiment described below, not a fresh-tape source theorem.

## Exact target and timing

`NestedCircleMass.lean` defines a continuation-valued finite-coin retry
experiment. An ordinary draw returns either failure or `(parameter, next
history)`. The next history can contain all consumed source state. The required
one-step law is explicit at **every** history: each fixed QM31 value has
unconditional mass `u = σ/P⁴`. Here `σ` remains symbolic; failures are included
in the averaging space, not conditioned away.

The source secure-circle map accepts exactly the parameters with nonzero
CM31-imaginary coordinate. Its excluded set has cardinality `P²`; the two
singular parameters are inside this set and are not charged separately.
Consequently, with

    u = σ/P⁴,
    r = P²*u,
    w = u*(1+r+r²),

each admissible parameter has mass `w` after one circle call with three
attempts. Ordinary failure aborts immediately. Only a successful excluded
parameter spends another inner attempt.

The distinct-second wrapper performs at most three **complete circle calls**.
It retries only on a successful point equal to the first point. The checked
source inverse makes this equivalent to equality of successful parameters.
A circle failure, including exhaustion of its three inner attempts, aborts
the wrapper immediately; it does not spend another outer attempt.

For fixed distinct admissible parameters `(t₀,t₁)`, the checked exact
unconditional mass of the ordered pair is

    w²*(1+w+w²).

The arbitrary `between : parameter → history → history` update occurs after
the first successful parameter and before the second sampler. It may encode
adaptive first-point answer absorption. Both target parameters are fixed
outside the sampling experiment. The same mass holds for every such ordered
pair and every initial history satisfying the uniform-law premise.

## Reused and new interfaces

- `BoundedRetryKernel.mass_three` supplies the scalar geometric retry law.
  The new generic `pay` kernel retains successful returned histories, so the
  second sampler can be used as the first sampler's continuation.
- `OrdinaryPrefixMass.unconditional_mass` is the checked actual one-call
  four-block decoder law, including abort and the exact rounded block cut.
  `decoded_ordinary_uniform` specializes its value law to a four-block coin
  kernel with an arbitrary returned history update.
- `SecureCircleParameterDomain.admissible_iff` and
  `zero_imaginary_card` derive the rejection mass, not an assumed rejection
  probability.
- `SecureCircleParameterInverse.successful_decoded_parameters_equal`
  supplies the actual parameter/point injectivity used by the outer duplicate
  comparison.

## What this does not prove

The abstract conditional history-uniform law is not discharged for the actual
sequential transcript. Nor is the continuation kernel yet identified with the
literal nested source decoder on a single chronological tape. Four-block
padding is an auxiliary coin space, not permission to advance the real cursor
by four or reveal unused blocks in a causal history. Those routing/refinement
obligations remain separate.

In particular, separate labels do not prove fresh hash inputs; successful
decoding does not justify conditioning away failures; two ideal independent
circle labels do not implement the source's nested abort order. No OOD root-set
probability, FS coupling, component recovery, extraction, or payment-security
bound is claimed by this leaf.

The proof uses only current checked imports, symbolic finite sums, and the
small retry identities. No QM31 or coin space enumeration was performed.

## Focused evidence

Both attempts used the existing pinned NUC overlay through Tailscale
`100.108.41.90` (the hostname alias was only for the pinned SSH host key).
Preflight found 46,810,312,704 bytes available and no active compiler scope.
Lean 4.32.0 ran with `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0, CPU 200%, module recursion depth 200 and 250,000 heartbeats.
Source parent `d0e31968…` is separate from the inherited runner's research
pin `289d7356…` and reused V7 pin `26a9cd47…`.

- `nested-circle-mass-nuc-v1`: exit 1, 3.15s, peak RSS 6,821,956 KiB, zero
  swaps. Local proof-plumbing errors concerned applying the named uniform
  hypothesis under a finite sum, explicitly unfolding `none` branches,
  reducing a true conditional, and a misspelled Option constructor lemma.
  The failed source snapshot, log and manifest are retained.
- `nested-circle-mass-nuc-v2`: exit 0, 3.36s, peak RSS 6,855,924 KiB, zero
  swaps. All eleven audits use only `propext`, `Classical.choice` and
  `Quot.sound`; there were no warnings. Provenance passed all 877 entries
  before and after the check and remained unchanged.

The repair used an explicit finite-sum congruence and local constructor
simplifications. No theorem hypothesis, retry semantics, memory, recursion
or heartbeat limit was changed.

Green source/snapshot SHA-256:
`53f004273ef3b332f7c259aebadcc2f2cbbcd1537e955dcc7cd2788402701308`.
Green output:
`1287dbe820f255fdef14c285e1b0f47401de84ea1386e0c4aab937a3c68a2e8a`.
Green manifest:
`6f99bac9a5e8bce4e253c2a265ec54add89c06daf8a746f9378c63cd77a6507d`.
Artifacts are retained under `experiments/`, alongside the new source.
