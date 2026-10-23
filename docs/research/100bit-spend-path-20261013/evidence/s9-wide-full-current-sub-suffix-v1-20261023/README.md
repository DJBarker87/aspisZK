# Checked QM subtraction tail, WideExact.mul source formula

This focused result maps the final two qcut `QM31.sub` operations to `CurrentWide` under the same canonical-input contracts. The first subtraction result's canonicality is derived from that same successful source call; the theorem preserves the complete `Result` behavior. It is one named suffix of the wider multiplication formula, not the whole formula theorem.

The accepted source uses the explicit Shared/Actual Result-mapper adapter at the imported operation-call boundary. The earlier unchanged source (retained under `diagnostics/`) exhausted the focused Lean memory budget while attempting to unify the two mapper heads over an opaque generated call. The accepted version uses the compiled mapper-head adapter and completed at the ordinary cap; it does not increase the cap or unfold generated arithmetic.

The packet contains no compiled objects. Its object hash is metadata in the receipt only. The axiom report is standard Lean (`propext`, `Classical.choice`, `Quot.sound`).
