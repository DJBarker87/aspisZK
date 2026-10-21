# EbyK first push and finish product

This focused Lean 4.32 proof instantiates the accepted concrete EbyK source-model operations. It starts with the installed constructor, performs one successful push under canonical-value and scalar-coordinate bounds, then calls the concrete finish operation. The returned current-Wide value decodes to the one-term scalar product.

The statement does not include the enclosing `Weights::pair` iteration, does not bind PairCut `weights.field` to the parser implementation, and does not establish Rust Std or full caller refinement. Those boundaries remain explicit. The generated PairCut external axiom closure is not imported as a theorem premise.

`manifest.json` records the exact source/object/receipt pins, selected direct-import owners, resource metrics, and standard axiom audit.
