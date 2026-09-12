# Selected semantic packing: exact Boolean writer and off-domain obstruction

Status: **packing/layout bridge proved; proposed off-domain MLE shortcut
rejected**.

`lean/SelectedSemanticPackedLiteral.lean` gives an explicit inverse for all 94
positions emitted by the selected Rust `semantic_packed` range order.  It proves
the exact lane/slot indices, the zero structural padding at position 95, the
positive residual insertion at position 94 (last pack, slot 2), equality of all
24 resulting Boolean-row packs, and their handoff to the recovery model's
`semanticMLE`.

The tempting stronger claim that the actual off-domain Rust
`semantic_packed(point)` equals the multilinear extension of those Boolean
values is false.  The source evaluator is a degree-27 polynomial in the
sumcheck point; its Boolean restriction does not determine its off-domain
value.  `boolean_writer_does_not_determine_source_semantic` preserves the
existing minimal Booleanity counterexample: a source term can vanish on the
whole Boolean table (and hence have zero table MLE) while being nonzero at an
ordinary off-domain point.

Accordingly, `callbackLanes_semantic_eq_boolean_writer` is deliberately a
Boolean-writer/recovery-model theorem, not a literal source-callback theorem.
The remaining valid route is to construct the actual degree-27 polynomial from
the selected Rust selector/opening/helper arithmetic and connect that
polynomial to the causal source trace.  Replacing it by an MLE identity would
hide a false premise.

## Focused evidence

- Base revision: `bb07caea`.
- Target: `SelectedSemanticPackedLiteral.lean`.
- Source SHA-256:
  `97f789e21311df5584f34cb67c741ba4216459423bf9b452ed2f2b1ea22766c8`.
- Olean SHA-256:
  `17a96450cefb3c7b9ef23228ad660a45f05f87dc108676a939d9943775f8cad5`.
- Pinned Lean 4.32.0 NUC compile: exit 0, wall 3.99 seconds, peak RSS
  6,593,712 KiB, swap 0.
- Cgroup: `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, bounded runtime.
- Printed axioms are a subset of `propext`, `Classical.choice`, `Quot.sound`;
  no `sorryAx`.

This is a deterministic formalisation result.  It changes no protocol or proof
bytes and supplies no probability term.
