# Analysis-reference independence of the relation game

Source pin: `bbca32e0e30be2c489c6437dd670da164e6d852f`.
Status: **kernel-checked deterministic field/source-shaped interface**, not
a new error term.
No verifier, transcript, Rust, proof-body or production changes are made.

The geometric cover chooses a quotient from the received word's mathematical
geometry. To use that choice in the security argument, one must establish
that inserting it as the **analysis reference** does not change the execution
being bounded. [ReferenceIndependentRelation.lean](experiments/ReferenceIndependentRelation.lean) establishes that property
for the retained compact grammar, rather than assuming equivalent execution.

## Exact interface

`replaceRows rows Q` changes only `Rows.referenceQ`. All four original
functionals and claimed scalars, the reconstruction map, interpolant,
quarter, and chord coefficients remain unchanged. The same kappa-dependent
strategy supplies all responses and actual finals.

`replaceOracle oracle Q` preserves the received slots and circle coordinates
exactly. Its support bookkeeping becomes `FixedOracle D D Q`: changing Q
cannot in general preserve a small-radius agreement certificate. The selected
received-word constructor already uses D D, so no selected support is lost.

The following executed quantities do not contain the reference:

- The transported ordinary functional and affine corrected claim.
- The image-augmented weights and their first dual fold.
- The carried compact scalar, post-query weights and post-query scalar.
- The raw compact suffix and its actual terminal dot-product acceptance.

`rows_accepts_iff` proves identical acceptance for every fixed challenge
sequence, including malformed later-challenge-list lengths rejected by the
retained grammar. It does not claim a parser or authenticated-byte refinement.

The proof also establishes `supported_rows_probability`: with the same
support predicate, the entire finite kappa/tau/alpha/query/rho/later-response
probability is unchanged. A separate `tail_probability` lemma eliminates the
dependent discrepancy equality used to index `Rounds` by equality induction;
the full constructed `After.prob` equality also reduces directly by
congruence on the unchanged data. The game itself is still
generated from actual weights, values and claims; it is not replaced by a
supplied Boolean success function.

## Essential limitation

The **support predicate is held fixed**. Replacing a reference while changing
the definition of which executions count as supported need not preserve its
event probability. The [checked geometric composition](pre-anchor-joint-continuation.md)
first defines the event from the same received word and actual final, then
applies the reference replacement to that event. Source/FS causality and efficient extraction
remain separate; this deterministic equality earns no probabilistic credit.

## Reproduction

Run from this research directory with a fresh output log name:

```
bash experiments/run_reference_independent_relation.sh experiments/reference-independent-relation-v2.log
```

The runner pins the retained source closure and the newly checked
`RepresentedImageGame` source/olean, checks provenance before and after the
focused leaf, uses `-M7000` and an independent aggregate 7 GiB guard, and
records wall time, peak RSS, swap, exit and axiom audits.

The [successful v2 log](experiments/reference-independent-relation-v2.log)
records exit **0**, **10.93 seconds**, peak RSS **5,607,014,400 bytes**,
**0 swaps**, and unchanged source/cache provenance. All eleven requested
axiom audits contain only `propext`, `Classical.choice` and `Quot.sound`.
There are no retained `sorry` or new axioms. The check used Lean 4.32.0 and
cached mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`.

| Artifact | SHA-256 |
|---|---|
| ReferenceIndependentRelation.lean | `68e98e5d5995cec09fcac9f4d6dc4e0ff286541511aa4efa44a15c839b328429` |
| ReferenceIndependentRelation.olean | `a75e48ce63d748eb402837bf4288e38a962089b40036b34a32d0ec64c5120e86` |
| Runner | `64582f439c322461809ff33e6afad72fee1d91701fd52ff98047315b59714b62` |

The [v1 diagnostic](experiments/reference-independent-relation-v1.log)
preserves two ordinary proof-script issues: one congruence had already closed
its goal, and eager congruence over nested averages reached the elaborator's
recursion limit. Explicit congruence on the finite-average functions avoids
that normalization. The resource cap was not raised; no unchanged large
dependency or runtime suite was replayed.
