# R17 witness transport and the adaptive-prefix boundary

Date: 2026-09-21. Source revision
`c7ef396740503eefeac1e9b662971b66b80741fc` plus this changeset.

## Three-block finite transport

`lean/AspisV8R17/WitnessShear.lean` defines an explicit equivalence

`(c,h,g) -> (c+dc, h+dh(c), g+dg(c,h))`.

The inverse first recovers c, then h, then g. Neither dh nor dg needs to
be linear. In particular, dg may depend on nonlinear witness/C1/helper
interactions. It may not depend on g itself. This is translation of the
existing coins, not resampling them after disclosure.

The observation model has four components: C1 view, a joint C1/H1 view,
G's retained view, and a shared contribution from C1/H1 plus a linear G
contribution. With explicitly quantified correction identities for **every**
c and h, Lean proves equality of observations under the equivalence and
equality of their finite uniform laws. It extends the earlier two-block
context shear to the actual three-stage candidate construction.

The corresponding source candidates in `r17_c1_witness_audit.rs` are:

| Block | Candidate dependence at fixed prefix | Required source premise |
| --- | --- | --- |
| C1 | Balanced compiler difference, legal inventory and prefix | Legal M31 free-coordinate translation, all original equations universally |
| H1 | Rebuilt helper difference, C1 correction and prefix | Legal balanced pad and joint-view equality universally |
| G | Full old/new C1/H1 terminal difference and ordinary quotient residual | Independence from old G; compatible-image coverage and retained-view equations universally |

The v16 tests evaluate these equations at two actual contexts. They do not
instantiate their universal quantifiers. The source terminal's structured
G addition gives a route to proving cancellation of old G in the target;
the literal Rust terminal/refinement theorem is still required. Legal
free-coordinate spaces, rather than unconstrained full masked trace arrays,
must instantiate C and H. The real seed-derived masks are not asserted to
be uniform elements of these product groups.

## Selecting a transport using a realized prefix

`lean/AspisV8R17/AdaptivePrefix.lean` proves an additional equivalence for
a prefix-indexed family e(p). Its premises require:

- If x realizes left prefix p, e(p)(x) realizes right prefix p.
- If y realizes right prefix p, e(p) inverse(y) realizes left prefix p.

Under those premises, choosing e using the realized prefix is bijective.
An observation-commutation premise then yields the finite uniform-law
result. These are explicit source obligations, **not new hiding assumptions**.

The same file proves a counterexample to dropping those premises. For a
Boolean prefix p, take identity when p is false and Boolean negation when
p is true. Each map is bijective. Selecting p equal to the input maps both
inputs to false. Thus a family of fixed-prefix bijections need not yield
an adaptive bijection. This is a generic counterexample, not a new V8 attack.

## First remaining source proposition

Universal compatible-image coverage and an explicit exceptional-event bound
are still missing for the source C1/H1/G targets and query schedules.
The required source-prefix invariants are also not established: the tested
coin corrections alter unobserved committed messages, and the diagnostic
does not preserve roots/frontiers or derive equal oracle challenges.

Do not apply `adaptivePrefixEquiv` to real mask coins while silently holding
the hash tape or commitment roots fixed. The retained R8 witness-retaining
paired-commitment hop and R9 operational/first-hit/memoized-expansion bridge
remain the intended route for handling that chronology. Their source trace,
query-budget and seed premises must be discharged for the new profile;
the three unavailable nonhost preimages are not waived. A public-only
simulator, visible failures/retries/publication and malicious-prover
soundness remain separate obligations. These two leaves prove no end-to-end
V8 privacy theorem or loss bound.

## Exact focused compilation

Cached workspace `/Users/dominic/ZK/AspisFormal`, inherited mathlib cache;
local `target/r17-lean` and `target/r16-lean` prepended to `LEAN_PATH`.
Commands use `lake env lean -j1 -M1800 -R <research/lean> -o <target> <leaf>`
(via an environment-only Python launcher), measured by `/usr/bin/time -l`.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| WitnessShear.lean | 0 | 9.91 | 1366147072 | 0 |
| AdaptivePrefix.lean, initial elaboration failure | 1 | 5.44 | 1286569984 | 0 |
| AdaptivePrefix.lean, explicit beta-normalized goals | 0 | 3.97 | 1299202048 | 0 |

The failed attempt's rewrite did not expose the composed lambda expression.
Two `change` steps fixed the proof without changing the statement. That
failed log reports `sorryAx` from elaboration errors and is **not** accepted
proof evidence. The successful final logs contain no `sorryAx`.

Final `#print axioms` results: witnessShear uses propext; witness commutation
uses propext/Quot.sound; both uniform-law theorems use only propext,
Classical.choice and Quot.sound. adaptivePrefixEquiv uses Quot.sound;
prefixFlip bijectivity uses propext/Quot.sound; the constant-map and
noninjectivity counterexample theorems have no axioms.

Logs under `/tmp/aspis-r15-host.drHYn9`: `r17-witness-shear-lean.log`,
`r17-adaptive-prefix-lean.log` (failed),
`r17-adaptive-prefix-lean-v2.log` (accepted). No Rust/protocol source changed,
no unchanged runtime suite or full manifest was replayed, and this is not a
formal release claim.
