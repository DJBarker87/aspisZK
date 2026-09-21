# R17 source-shaped algebra bridge

## Legal balanced coordinates through full mixing — 2026-09-21

Base `110e18ca12fc6e5b08696c17cf8dcb28ef5a314a` plus this changeset.
LegalMaskCoordinates.lean reuses the R16 balance operation and constructs an
explicit equivalence from all non-pivot coordinates to vectors with inactive
sum zero. Active coordinates are preserved; they are not summed into that
constraint. The dependent coordinate is reconstructed, and every already-legal
vector is a fixed point of balancing. Theorems also show that an overwritten
pivot value has no effect on the final balanced vector.

LegalSourceMixing.lean carries this legal space through the COMPLETE retained
mixing1024 equivalence. Its transformed constraint is the inactive sum of the
inverse-mixed vector, not zero in an arbitrarily selected mixed coordinate.
It composes free-coordinate parametrization with legal mixing and identifies
each resulting coordinate with the source-shaped Horner loop. Forward and
inverse mixing are additive; so is the transformed balance constraint.
For an already-legal mixed vector, adding delta preserves legality iff delta
has zero transformed balance constraint. All 1024 mixed coordinates remain
present; no uniform independent 271-coordinate prefix law is asserted.

Re-inspected state_only_hiding.rs first_inactive_row and
balance_qm31_copy_inactive: the G/main-mask builder selects its first inactive
row, whereas the separate R16 transport uses its own fixed pivot. Do not
silently replace the builder's dependent coordinate with the transport pivot.
The lemmas parameterize the inactive set and pivot with explicit membership;
concrete source inventory/refinement is still required for instantiation.

The overwritten-draw theorem concerns the VALUE after successful sampling.
The source still draws that coordinate: its retries, consumed words, hash
queries and possible exhaustion cannot be removed from a distribution or
failure proof. Similarly, an exact free-coordinate equivalence does not by
itself make seed-expanded source masks uniform on that space.

This supplies a legal-space adapter for the joint posterior route, not joint
C1/H1/G coverage. The next central proposition remains solving every required
affine witness-offset target inside the legal space while retaining all
raw/point/OOD/final/semantic/relation observations. The source field model,
adaptive-prefix and full commitment/oracle/seed/failure/publication/soundness
obligations remain open; no additional hiding assumption was added.

Focused cached lake commands use -j1 -M1800, -R research/lean and matching
r17 objects, smallest generic leaf before dependent bridge:

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| LegalMaskCoordinates.lean, five audited declarations | 0 | 8.24 | 1329790976 | 0 |
| LegalSourceMixing.lean, seven audited declarations | 0 | 8.41 | 1781940224 | 0 |

All twelve #print axioms results use only propext, Classical.choice,
Quot.sound. Both leaves compile without warnings. No production/source
sampler change, runtime replay or full manifest replay occurred.

## Horner mixing bridge and duplicate-declaration repair — 2026-09-21

Base `14f6ce72ccfafc17491aab3eb3a99a1af76d97ec` plus this changeset.
Inspection found that retained TerminalG.lean (commit d7692b0c) already
defined replacedGTerminal/replacedGTerminal_eq, with the positive-transfer
extra term retained, and proved old-G independence including cube sums.
The preceding SourceZeroBoundary leaf had duplicated those declaration names.
Its standalone compile did not establish compatibility with TerminalG.

The duplicate definitions and redundant terminal wrappers are now removed;
SourceZeroBoundary imports TerminalG and retains its five new loop/composition
theorems. No earlier terminal theorem, negative regression, or source premise
was removed. This supersedes the previous section's claim of eight new
integrated declarations: three terminal audits were redundant, and two names
collided across modules. The final dependent compile below includes both
retained TerminalG and corrected SourceZeroBoundary.

New SourceMixing.lean proves six facts about the literal reverse-list Horner
loop used by mixed_coins: its cons recurrence, finite power-sum expression,
additivity in coefficients, equality to the retained mix definition, equality
to mixing1024, and identification of the source's first 271 outputs with the
prefix of that complete equivalence. The field/characteristic premises are
those of the retained Mixing module, not new hiding assumptions.

This does not call the 271-coordinate projection a bijection. The remaining
753 transformed coordinates are not discarded from the posterior. In
particular the source G vector has an inactive balancing constraint; a
bijection on the unrestricted 1024-dimensional space does not establish the
law on that legal subspace. Joint retained-observation coverage and legal
mask-space source correspondence remain required before applying WitnessShear.
The concrete Rust scalar conversion, slice bounds and QM31 implementation
refinement also remain explicit obligations.

The initial prefix corollary hit elaborator recursion-depth while inferring
the Fin 1024 index. Supplying that index explicitly and proving its bound
symbolically fixed the failure; no recursion or memory cap was raised and
no 1024-term numerical evaluation was introduced.

Focused cached lake commands use -j1 -M1800, -R research/lean and matching
r17 objects. No production or Rust source changed, no runtime replay.

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| SourceZeroBoundary importing retained TerminalG | 0 | 10.24 | 1695907840 | 0 |
| SourceMixing, implicit prefix index failed | 1 | 10.17 | 1769177088 | 0 |
| SourceMixing final integrated bridge | 0 | 7.42 | 1784348672 | 0 |

Final five SourceZeroBoundary and six SourceMixing audits use only propext,
Classical.choice and Quot.sound (Horner cons omits choice). Failed sorryAx
output is rejected. SourceMixing has no warnings; prior unused-simp warnings
in SourceZeroBoundary remain. The source anchor r17_structured_g.rs is unchanged.

## Inner power loop and old-G cancellation — 2026-09-21

Base `9d75a42346c4298a9b119d87d0a5aa772ec05117` plus this changeset.
`AspisV8R17/SourceZeroBoundary.lean` closes the inner polynomial-loop algebra
left open below. For any width, start power x^k and accumulator out, the
literal fold updating `(out+c*(power-x), power*x)` equals the finite sum
`out + sum_i c_i*(x^(k+i)-x)` and final power x^(k+width). The proof uses
structural induction, not concrete recurrence normalization.

With k=2 and initial accumulator a*(1-(x+x)), this is exactly roundEval.
The source-shaped evaluator is additive in all coefficient inputs. Its
per-round contributions now compose with the retained reverseMaskAccumulator
and SourceMaskLoop theorem to equal structuredMask for every round count.
The source parameters are 26 tail coefficients plus a, ten rounds. Array
slicing/index bounds and concrete QM31 operations still need Rust refinement.

Three further identities prove the staged terminal replacement
`(base + factor*g) - g*factor + g = base+g`, cancellation of the same old g
from an old/new context difference, and correction by delta=leftBase-rightBase.
These algebraic identities hold for arbitrary inputs. They remove one reason
the correction target might depend on old G; they do not by themselves prove
that every source base term, relation target and correction algorithm is
independent of old G or instantiate WitnessShear's universal premises.

Source inspection: core state_only_selected_mask_value computes the C1/mask-only
Horner value then adds `(1+explicit_linear^26)*g`; the statement masked terminal
adds eta*original. composition_parts/terminal_parts carry g separately from
original. Both staged payment terminals subtract claims[27]*explicit_g_factor
and add claims[27]. The positive-transfer correction is separate and must
retain its own C1 dependence. No existing inactive-H1 term was deleted.

Rechecked anchors:

| Source | SHA-256 |
| --- | --- |
| tools/r17_structured_g.rs | 147be74e8651e05aa4680dbb412252751e8f21f5a6ad8a4de939d0f01bfb52c6 |
| core state_only_hiding.rs | 18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f |
| statement pair_forest_semantic_terminal.rs | efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58 |
| staged v19 payment_extraction.rs | da7a86f30290031f8d48d982c886f7cff676b38f80b67df25638382000c8e6ae |

The current source is still a research repair, not production. The next
central obligation is universal compatible-image coverage for the C1/H1/G
affine witness offsets and all retained observations, with the source
old-G-independence and legal-coordinate maps justified. Fixed-prefix examples,
the active minor, and these scalar identities are not that complete result.
Adaptive-prefix, commitments/oracle/seed, failures/publication, simulator and
malicious-prover soundness obligations remain separate.

Focused cached lake command: -j1 -M1800, -R research/lean, matching
target/r17-lean/AspisV8R17/SourceZeroBoundary.olean. No full replay or runtime
rerun; production source and negative regressions unchanged.

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Inner loop and terminal cancellation, six audits | 0 | 10.18 | 1691648000 | 0 |
| Added full mask-loop composition, eight audits | 0 | 5.12 | 1697316864 | 0 |

All eight #print axioms audits use only propext, Quot.sound and (for the
finite sums/structured composition) Classical.choice. No sorryAx or new
assumptions. Two unused-simp warnings remain.

Date: 2026-09-20. Base revision
`0bcca87a835fcb050328c58deb18a440b26d237e`, plus this proof changeset.
No Rust or protocol source changed. These are universal algebraic results,
not a complete Rust semantics, commitment extraction, or privacy proof.

## Reverse mask loop

`lean/AspisV8R17/SourceMaskLoop.lean` models the source's accumulator
`(out, scale)`, initially `(0,1)`, processing round contributions in reverse
order with `(out + contribution*scale, scale*half)`, then adding
`initial*scale`. It proves equality to a literal reverse-list `foldl`, not
just a recurrence asserted to resemble the loop.

For contributions given by the existing zero-boundary `roundEval`, the
accumulator equals `structuredMask` for every field with nonzero 2 and
every number of rounds. Therefore its full Boolean-cube sum is the initial
coordinate, and its next suffix sum is exactly `semanticRound`. This
connects the reverse source evaluation order to the previously proved
forward recurrence, without enumerating 1024 concrete Boolean inputs.

The source anchor is `tools/r17_structured_g.rs`, SHA-256
`147be74e8651e05aa4680dbb412252751e8f21f5a6ad8a4de939d0f01bfb52c6`.
Still required: the Rust array slicing/index order and `zero_boundary`
power loop refine the list of `roundEval` contributions, and QM31 operations
refine the abstract field. The theorem does not assume or prove those facts.

## Arbitrary-input channel errors

`lean/AspisV8R17/ChannelResidual.lean` proves the projected-claim identity
`u(all-g)+v(g) = u(all)+(v(g)-u(g))`, including its pullback through the
common additive transport. Here `g` represents the already gamma^27-scaled
G column and `all-g` the complementary batch.

More importantly, it retains malformed-input errors. For arbitrary
committed vectors, interpolants, submitted quotients and a claimed scalar,
the verifier's claimed-minus-quotient discrepancy equals:

1. the claimed scalar minus the true projected functional value;
2. the ordinary functional of the ordinary column/interpolant/quotient residual;
3. the G functional of the G column/interpolant/quotient residual.

There is **no premise that submitted quotients or claims are correct**.
Nor does the theorem infer that the three errors vanish individually when
their sum vanishes. That inference requires the actual independent checks,
extraction and batching bad-event accounting. This preserves, rather than
silently erases, the carried/ordinary error in the degree bounds.

Source anchor: `tools/r17_host_relation.rs`, SHA-256
`4778e671d2a41975d47961dcd699ec772ca9183321e496d37810180f15c63bfb`.
Its parser, packed G projection, gamma powers, functional construction and
opening authentication still need the exact source refinement/extraction
argument. The additive maps in this algebra are not that argument.

## Focused compilation and axioms

Cached workspace `/Users/dominic/ZK/AspisFormal`; each command uses
`lake env`, `lean -j1 -M1800 -R <pack>/lean`, with the existing
`target/r17-lean` and `target/r16-lean` prepended to `LEAN_PATH`. Outputs
are the matching `.olean` files in `target/r17-lean/AspisV8R17`.
No package-wide replay or unchanged Rust suite was run.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| `ChannelResidual.lean` | 0 | 8.84 | 1353269248 | 0 |
| `SourceMaskLoop.lean`, initial bridge | 0 | 6.91 | 1686519808 | 0 |
| `SourceMaskLoop.lean`, added reverse-fold and suffix endpoints | 0 | 2.49 | 1695170560 | 0 |

All four channel endpoints and all six audited mask endpoints report only
subsets of `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, new
axiom, distribution assumption or hiding assumption is added.
Logs: `/tmp/aspis-r15-host.drHYn9/r17-channel-residual-lean.log`,
`r17-source-mask-loop-lean.log`, `r17-source-mask-loop-final-lean.log`.

## Remaining boundary

The loop-order and arbitrary-input residual algebra are now proved. The
first remaining source bridge is the concrete field/index/packed-column
refinement just identified, composed with the transported chord weights.
The joint H1/G causal posterior, adaptive exceptional-event bounds,
commitment/shared-oracle/seed expansion, and failure/retry/publication laws
remain necessary. Neither these algebraic identities nor the prior host
acceptance tests establish full privacy or malicious-prover soundness.
