# S4 29×4 reconstruction integration

Base: `6279cccf41ffc0c67008918992d3a1cf6e45f6f3`.

This note records the independent S4 extraction-algebra ticket.  It does not
claim a replay collector, a permitted-access extractor, an accepted payment
witness, an actual-verifier refinement, or a global soundness result.

## Checked algebraic endpoint

`lean/FSV8S4MatrixReconstruction.lean` adds the finite-data construction

```text
29 distinct gamma rows × 4 distinct alpha nodes per row
  -> 29 × 1024 reconstructed component coefficients.
```

The construction reads only final vectors and public OOD data.  Its central
theorems show that, if each node has the stated quotient/fold representation,
then reconstruction identifies the common tuple; and if those tuples lie in a
single fixed family, the computed tuple belongs to that family.

`lean/FSV8S4RecoveredHighMatrix.lean` composes that result with the literal
`RecoveredHigh` event.  It keeps the adaptive `final` values from
`Execution.strategy`, same-gamma high-support uniqueness, and the fixed
family of cardinality at most one.  Its two endpoints are:

- `recovered_high_matrix_constructs_family_member`;
- `recovered_high_matrix_has_early_projection`.

The second transports the early-C1 membership supplied by `RecoveredHigh` to
the *computed* tuple.  It does not enumerate `EarlyC1Family`, test the
noncomputable classifier, or validate a payment.

The integration repair is source-level and deterministic: the recovered
event expresses the original message through `(atGamma e.data gamma).original`,
while the finite-data kernel uses `ComponentRows.original`.  The composition
now uses the checked definitional bridge
`SelectedComponentGame.original_eq`; it does not equate unrelated chord maps.

## Focused checks

Pack integrity was checked with `sha256sum -c SHA256SUMS` from
`aspis-v8-soundness-s4-endgame-pack-20260913`.

```text
python3 scripts/full_matrix.py --json /tmp/s4-full-matrix.json
```

passed on 2026-09-13.  The source-sized synthetic fixture reconstructs all
29,696 coefficients from 116 `final256` vectors (475,136 canonical scalar
bytes), verifies 59,392 nodal equalities and 29 image conditions.  Its digest
is `72630923a6eb94cd823edc8ac07a29c8ab1bad06296a8f1fa47763ea383aef75`.
This is reference arithmetic, not an Aspis replay or a source refinement.

```text
python3 scripts/verify.py
```

passed 76/76 S4 Python tests.  The tests are finite/reference checks only.

On the NUC via Tailscale, pinned Lean `4.32.0`
(`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), each leaf was compiled in a
separate `systemd-run --user --scope` with `MemoryHigh=7500M`,
`MemoryMax=8G`, and `MemorySwapMax=0`:

| Target | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8S4MatrixReconstruction.lean` | 0 | 3.12 s | 6,735,324 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8S4RecoveredHighMatrix.lean` | 0 | 2.89 s | 6,735,708 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |

The `#print axioms` output for all promoted declarations contains no
`sorryAx` and no new custom axiom.  This is a focused compilation and axiom
audit, not a clean first-party rebuild or external kernel replay.

The packet source-pin check also passed for all 30 selected files at the base
commit.  It is an identity check, not a source-to-Lean refinement theorem.

## Explicitly open

The premises of the recovered-high composition still require all 116 nodes to
be actual usable continuations from one fixed pre-gamma setting.  Producing
those nodes with permitted replay/restoration access, preserving cached output
semantics, bounding collection failure, and proving source-event lineage are
open.  The finite-data kernel accepts arbitrary final vectors algebraically;
interpolation alone is not evidence of acceptance or recoverability.

Likewise, family membership and early-C1 projection do not establish usable
node availability, C1 decoding access, semantic/copy constraints, ownership,
the checked payment/context/settlement predicate, or Fiat--Shamir coupling.
Those boundaries remain separate from this deterministic algebra.
