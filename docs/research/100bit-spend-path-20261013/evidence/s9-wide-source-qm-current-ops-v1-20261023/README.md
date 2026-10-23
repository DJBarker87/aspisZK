# Actual source QM add/sub to CurrentWide maps

This focused Lean result proves full-`Result` maps for the transparent selected-source `QM31.add` and `QM31.sub` bodies to the checked `CurrentWide` operations. The qcut-to-current comparisons retain the fail/div branches. For wrapping source arithmetic versus checked CurrentWide arithmetic, each theorem states canonical input requirements and derives the required successful intermediate results from the corresponding qcut operation semantics.

The sub path uses the actual two `CM31.sub` calls exposed by the qcut, then the probe/CurrentWide bridge. It does not claim unrestricted equivalence for noncanonical inputs, and it does not prove the wider `WideExact.mul` composition by itself. This packet includes source and receipts only; no compiled Lean object is included. The recorded `#print axioms` reports are standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
