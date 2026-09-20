# R17 mixed round-mask algebra and source opening boundary

Date: 2026-09-20. Base revision `92e0e013` plus the files committed with this
ledger. This is a research prototype, not a repaired source profile, a full
privacy theorem, or a soundness-preservation verdict.

## Construction and compiled algebra

Keep the existing 1024 QM31 G coordinates. Apply the fixed square mixing
map `u[i] = sum_j G[j] * (i+1)^j`, with nodes 1..1024. The first 271 outputs
are the initial scalar and 27 coordinates for each of ten zero-boundary
polynomials from `R17_STRUCTURED_G_CANDIDATE.md`. The other 753 outputs are
retained coordinates, not fresh randomness.

The following leaves in `lean/AspisV8R17` compile:

- `Mixing.lean`: evaluation at distinct nodes is injective by the polynomial
  root bound. Over a finite field it is bijective. Nodes 1..1024 are proved
  distinct in characteristic 2147483647, giving `mixing1024`. `mix_apply`
  identifies the map with the explicit power-sum matrix. This uses no new
  hiding assumption. Refinement of QM31's implementation and its actual
  entropy-backed seed distribution remains separate.
- `StructuredRound.lean`: zero-boundary identity, exact coefficients at
  degree 0 and degrees 2..27 (width=26), degree at most 27, the carry
  boundary equation, and the invertible compact-coordinate shift. None
  divides by a verifier challenge.
- `CausalRounds.lean`: an explicit bijection for any number of additive
  causal cuts; an initial scalar is output before its resulting state is
  constructed. A context-to-transcript-fiber equivalence retains the
  context instead of resampling it. The signature requires that offsets
  and state updates cannot inspect future coins. It does **not** justify
  fixing a real G-dependent commitment root while assuming independent
  uniform G coins. The paired-commitment/oracle source premise is still open.
- `StructuredCube.lean`: the recursively defined structured mask sums to
  its initial scalar over every Boolean cube, and after any processed
  prefix its suffix sum is exactly half the carry plus the next
  zero-boundary polynomial. This is universal in the number of rounds.
- `SharedBatchBoundary.lean`: two different additive functionals cannot
  both be evaluated by any function of their single summed input. This
  records a necessary source integration boundary, discussed below.

These are source-shaped algebraic models, not Rust extraction. All audited
declarations use only subsets of `propext`, `Classical.choice`, `Quot.sound`;
no `sorryAx` or user-added axiom occurs in the successful targets.

## Executable prototype and compatible-image check

`tools/r17_structured_g.rs` is included only in the existing test-only R16
module. It implements the power-sum mixing, structured evaluation, compact
round coefficients, and the terminal linear weights.

Its focused algebra test compares Horner mixing with every one of the 271
explicit rows; sums over the full 1024-point Boolean cube; checks all ten
rounds, their boundaries and coefficient recovery; compares 290 suffix
sums (28 interpolation points and one extension-field point per round);
and checks the final carry and the terminal functional against direct
evaluation. No production or staged R16 host path was changed.

The mixed placement has rank **596 of 618** in the fixed R16 PCS fixture,
exactly matching the upper bound from the 22 independent fold relations.
The test checks the zero elimination remainder and an independent inverse
product on pivot columns. The first-271 direct-placement negative remains
rank **540**, and the original R16 positive remains rank **408 of 430**.

The 618 coordinates remain the 271 mixed coins, 88 raw G values, two old
MLE G point values, 256 G quotient final coefficients, and one inactive
claim, with the two OOD values fixed by the quotient parametrization. The
new first G claim is determined by the mixed coins and is not independent.
This fixed map is **not the transcript of an implemented protocol**. In
particular it cannot certify the extra messages required by a redesigned
opening argument.

## Source-specific obstruction: the existing PCS has one shared functional

The inspected R16 stage is
`/tmp/aspis-r15-host.drHYn9/r16-basis-source-v3`. Its three relevant files
under `docs/research/v8-no-work-100-20260907/experiments` match the retained
`r16-stage.json` post-edit hashes:

| Source file | SHA-256 |
| --- | --- |
| `performance.rs` | `512d31aa25f3e70172b16dc841e7696a720610d44a651894495cd03bc0272c07` |
| `inactive_row_binding.rs` | `801aaaa5e52a932979f8307eac02c733e7b699738db7fe3605234509ef6948c2` |
| `structured_weights.rs` | `5e03063543e65d5438e573dc359778a1732e5401ba043e1d433f6132f7b9155f` |

`performance.rs:217-239` batches all 29 columns into a single message,
decodes one quotient, applies one ordinary weight vector, and publishes
one Final256. `inactive_row_binding.rs:121-126` transports and transposes
the single weight vector used by the selected structured route.
`structured_weights.rs:94-130` batches each set of point and OOD claims
with the same gamma powers. Thus a G-specific functional cannot be
substituted merely by changing a common weight vector.

Algebraically, let ordinary first-point weights be w and proposed G
weights be v. Changing H1 by `-gamma*d` and G by d leaves the batched
message unchanged, but changes the proposed first-point batched claim by
`gamma^27 * <v-w,d>`. The negative regression constructs such a nonzero
change using a balanced inactive-row d; the actual H1 pad application
accepts the H1 change. The inactive sum remains unchanged as well.

This is an obstruction to the proposed shared-functional identity, **not
a forged proof or a soundness attack on the unchanged protocol**. Gamma
is fixed in the algebraic check; it is not a causal construction of two
real commitment/oracle executions. Adding a different inverse-dual common
weight cannot fix an identity that already fails before the invertible T.

## Exact next source proposition and possible route

Before source-instantiating the new mask, construct an opening argument
that binds the ordinary-column functional and the different G functional
to their respective committed messages, for malicious as well as honest
inputs. Reusing the one-quotient/shared-weight verifier is ruled out.

A concrete route to scrutinize is two quotient channels, not a new hiding
assumption. Let `c_R = sum_{j != 27} gamma^j T(m_j)` and
`c_G = gamma^27 T(G)`. With their respective OOD interpolants I_R and I_G,
write `c_R = I_R + L*q_R`, `c_G = I_G + L*q_G` for the common chord L.
If U is the ordinary original-row functional and
`V = U + kappa*(structured_G_weights - first_MLE_weights)`, the required
claim after subtracting the two interpolant contributions is

`<L^T T^(-T) U, q_R> + <L^T T^(-T) V, q_G>`.

This suggests a sum of two relation-polynomial computations, two separate
image constraints, and two sets of folded final coefficients and raw
quotient consistency checks. It is not implemented or proved here. Every
new visible value, challenge dependency, batching loss and image-gate loss
must be included in both security ledgers. In particular the existing
single-G compatible-image test does not prove privacy of the other channel
or of the new relation polynomials.

Independently, even the current 618-row candidate needs a bound on failure
of `rank(A(z,p0,p1,alpha,queries)) = 596` under the actual conditioned source
law, not just a nonzero minor at one fixture. Analogous C1/H1 obligations,
commitments, shared oracle, seed expansion, failures, retries and publication
remain open. No source pin, C1 negative, H1 incidence fact or retained
observation is waived.

## Focused execution evidence

Lean ran in `/Users/dominic/ZK/AspisFormal` using cached dependencies with
`/usr/bin/time -l lake env lean -j1 -M1800 -R <pack>/lean -o
<worktree>/target/r17-lean/AspisV8R17/<leaf>.olean <leaf>.lean`.
For `StructuredCube`, `lake env python3` only prepended `target/r17-lean`
to the inherited `LEAN_PATH` before executing the same Lean arguments.

| Final target | Exit | Wall seconds | Peak RSS bytes | Swap |
| --- | ---: | ---: | ---: | ---: |
| StructuredRound | 0 | 3.87 | 1692778496 | 0 |
| CausalRounds | 0 | 1.89 | 912359424 | 0 |
| Mixing | 0 | 4.88 | 1778401280 | 0 |
| StructuredCube | 0 | 6.56 | 1688272896 | 0 |
| SharedBatchBoundary | 0 | 5.05 | 809631744 | 0 |

Mixing's initial nonsingular-inverse version exceeded M1800 (exit 134,
4.23 s, RSS 1916731392, swap 0). An adjugate replacement still exceeded the
same cap (exit 134, 10.56 s, RSS 1916715008, swap 0). Inspection identified
the matrix dependency closure rather than a large concrete recurrence;
the replacement uses polynomial-root injectivity plus finite-field
bijectivity. It compiled under the **unchanged** cap. Missing import paths
and ordinary draft elaboration errors were corrected in focused files;
none is represented as a successful proof. No cold dependency build ran.

Rust commands used `/usr/bin/time -l cargo test --offline --locked --release
--jobs 1 -p aspis-prover --lib <filter> -- --nocapture`. Expected work was
focused compilation followed by optimized named field elimination or
the named algebra test, not proof generation or a full suite.

| Filter / changed scope | Exit | Wall seconds | Peak RSS bytes | Swap |
| --- | ---: | ---: | ---: | ---: |
| Initial `r17_structured_g_vandermonde_compatible_image` | 0 | 28.05 | 524304384 | 0 |
| `r17_structured_g_`: shared row implementation plus algebra and placement tests, 3 passed | 0 | 30.79 | 531316736 | 0 |
| Shared-functional negative, first unrestricted unit-vector version | 0 | 20.54 | 530612224 | 0 |
| `r16_g_posterior_including_final256_compatible_image`, refactored placement dispatch | 0 | 2.40 | 81166336 | 0 |
| `r17_structured_g_unchanged_shared_functional_negative`, strengthened to actual accepted balanced H1 pad | 0 | 19.79 | 531300352 | 0 |

The final negative uses inactive rows 0 and 1; its actual H1 pad acceptance
check passed, the combined delta was zero, and the required claim delta
was nonzero. Compilation took 19.31 s; the test took 0.01 s. No unchanged
full manifest, host replay, deployment, wallet operation or merge ran.
