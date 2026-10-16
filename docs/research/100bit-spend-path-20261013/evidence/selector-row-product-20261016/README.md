# Extracted selector tables and row products

`SelectorAtPointModel` composes the actual two fixed-size selector expansions from the extracted ten-coordinate source point. `SelectorRowSemantic.boxed_row_products` proves that the decoded high/low table product at the source shift/mask indices equals the existing selected-selector polynomial and its ten-factor tensor product for every row in `Fin 1024`.

The proofs reuse the existing selected-selector expansion and index arithmetic. They do not yet prove success/canonicality of the generated `Selectors.row` wrapper; that small source composition is the next target. These modules refine the extracted candidate slice, not the whole deployed verifier.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `SelectorAtPointModel` | 2.168 | 3824228 | 2 |
| `SelectorRowSemantic` | 1.951 | 3812216 | 1 |
