# Selected value/auxiliary source construction

Status: focused Lean proof complete for five additional semantic outputs;
literal Rust refinement remains open.

`SelectedValueAuxiliarySourcePolynomial.lean` constructs exact chronological
source polynomials for:

- auxiliary successor value;
- auxiliary XOR-12 value;
- both conservation equations; and
- the repaired positive-transfer product.

The sources use the actual row 1008/1010/1012 selector for auxiliary values,
row 1014 for conservation and positivity, and committed-table MLE openings
for the current, successor, and XOR-12 views. The positive expression has
its explicit degree-four proof; the linear outputs have degree at most two.
All therefore satisfy the selected degree-27 source grammar.

For every Boolean row, the development proves that each constructed source
table equals the lifted literal `SelectedSemanticRows.residual` coordinate.
The generic Boolean-suffix constructor then supplies every chronological
round boundary. No endpoint is assumed and no off-domain value is inferred
from Boolean-table equality.

Together with the previously constructed 30 range-bit outputs, 35 of the 95
selected semantic coordinates now have this source-polynomial construction.
The nearby recomposition coordinate remains open because the pinned Rust
uses reverse Horner evaluation; its equality to the corresponding linear
combination of opening tables must be connected explicitly. The pinned Rust
opening/selector memory path and the research wrapper's positive
`terminal_delta` also remain literal-source refinement obligations.

The focused NUC build used Lean 4.32.0 in a user systemd scope with
`MemoryHigh=9G`, `MemoryMax=10G`, and `MemorySwapMax=0`. It exited zero in
5.20 seconds, used 6,613,104 KiB peak RSS, reported zero swaps, and used only
`propext`, `Classical.choice`, and `Quot.sound`. Exact hashes and the complete
log are in
`results/v8-completion-fs-extraction-20260911/selected-value-auxiliary-source-v1/`.

This leaf changes no protocol, proof bytes, verifier acceptance, or security
ledger.
