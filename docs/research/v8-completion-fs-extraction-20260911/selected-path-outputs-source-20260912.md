# Selected path-output source construction

`lean/SelectedPathOutputsSourcePolynomial.lean` constructs chronological
degree-at-most-27 source polynomials for all seventeen path outputs:
direction Booleanity, eight left links and eight right links.

The construction uses the exact committed-table opening columns and signs of
the selected callback: direction reads `z[0]`; left limb `i` reads
`succ_z[i] - z[1+i]`; right limb `i` reads
`succ_z[8+i] - z[1+i]`.  The corresponding selector is the MLE of the literal
Boolean `pathMask`.  Each local coordinate slice has degree at most three.
For every Boolean row, the source table is proved equal to the lifted literal
`SelectedSemanticRows.residual` coordinate.  The generic Boolean-future-suffix
constructor supplies the chronological round boundaries without assuming an
endpoint.

An independently defined array-level `rustPathOutput` proves the literal
opening indices, direction/left/right order and producer-minus-consumer signs
equal the source values.  It takes the already constructed path-selector
functional as input.  Equality between the pinned Rust high/low factorised
selector calculation and that functional, and literal Rust/Aeneas machine
refinement, remain open.

Together with the thirty range outputs, five value/auxiliary outputs and the
recomposition output, this raises constructed semantic-coordinate coverage
from 36/95 to 53/95.  Initial/occupancy, absorption, public digest and scalar
outputs remain open.

The focused Lean 4.32.0 NUC replay exited 0 in 14.00 seconds with peak RSS
6,844,380 KiB and zero swaps.  All promoted declarations print only
`propext`, `Classical.choice`, and `Quot.sound`.  Exact evidence is under
`results/v8-completion-fs-extraction-20260911/selected-path-outputs-source-v1/`.
