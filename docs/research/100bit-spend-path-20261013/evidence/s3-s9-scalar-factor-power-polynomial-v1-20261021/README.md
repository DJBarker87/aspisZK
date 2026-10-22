# S3/S9 scalar-factor power polynomial

This source-only packet composes the successful emitted `scalar_factor` fourfold trace with the selected `kpowers` read-value theorem. It proves one output equation from one set of witnesses: each coefficient is the actual value read at `PERM[i]`, and each matching factor read decodes to `seed^i`. The output is the four-term polynomial followed by the quarter multiply.

The Lean release uses standard axioms only (`propext`, `Classical.choice`, `Quot.sound`). It retains the P6 iterator-fold law, canonical indexed-`p` read premise, successful selected `kpowers` result, and canonical seed. The source/Std `from_fn` bridge, enclosing `Weights::pair` caller refinement, and production adoption remain open. The polynomial is stated in decoded `WideExact` coordinates and keeps the four `PERM[i]` witness indices; it does not assume a numeric permutation table.

The exact FourFold, fold-step, and callback-operation sources and producing receipts are retained here, along with their selected direct-import owners and original producer packet manifests. No `.olean` files are included. Run `python3 check_packet.py` here to validate the source, object, receipt, and file pins.
