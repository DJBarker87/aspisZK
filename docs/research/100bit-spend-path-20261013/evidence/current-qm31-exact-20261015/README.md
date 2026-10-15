# QM31 tower and exact-field bridge evidence

This is the second, separate bundle. The first arithmetic bundle at `/tmp/aspis-r1-qm31-arithmetic-bundle-20261015` remains unchanged.

Seven focused Lean targets are green: `QM31WordFormulas`, `QM31WordResidues`, `QuadraticTowerOperations`, `QM31WordTower`, `ExtractedCurrentQM31Tower`, `ExactTowerBase`, and `ExtractedCurrentQM31Exact`. There are 26 public axiom reports across the successful targets; see the raw logs for the individual declarations and axioms. The failed `current-exact-field-a` attempt is preserved separately; attempt b replaces only the proof step with direct `exact hdecode`, with no theorem-premise change.

The unchanged V8 sources and the current extracted modules are pinned per source revision. The current `ExtractedCurrentQM31Mul` source/object is retained as a direct import dependency from the first arithmetic bundle. The clock measurements for `current-word-tower-a` differ substantially: receipt duration is 16.813 seconds while `/usr/bin/time` reports 767.63 seconds real. Both are recorded without an inferred cause.

This records focused Lean arithmetic components only. It makes no Rust/compiler refinement, protocol acceptance, or security-closure claim.
