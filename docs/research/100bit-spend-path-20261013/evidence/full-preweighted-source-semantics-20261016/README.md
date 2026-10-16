# Complete generated add_preweighted primitive to R0P packing

PreweightedApplyGroups gives a symbolic closed form for the traversal and proves contributions outside a nonempty source interval vanish. PreweightedWrapperModel combines the exact generated loop, checked wrapper arithmetic and zero padding: for any canonical input and packed arrays, N>0 and start+N<=96, actual add_preweighted succeeds, preserves canonicality and every one of its 24 decoded output cells equals its old value plus the correct mathematicalPack of the four selected source lanes.

PreweightedWrapperSemantic transports that complete actual-source result through the retained exact-tower embedding to the existing WideExact/R0P.pack4 semantics. It reuses the proved packer, field arithmetic, basis compatibility, array helper and inclusive-iterator runtime model. No opaque callback success or desired final-value equation is assumed.

SelectorValueLanePackScale proves the four-cell source packing formula respects a common selector factor from the four pointwise decoded multiplication equations. The enclosing value/semantic caller, commitment/extraction correspondence, final admitted source/artifact closure and complete security theorem remain open. This proof applies to the explicitly pinned modified-source candidate, not a newly rebuilt release program.

All focused Lean4.32 NUC targets exit0 with zero process swaps and only standard printed axioms. Exact source/import pins, commands, caps, wall/RSS/swap receipts and reports are retained. Symbolic induction avoids normalizing concrete 24-group recurrences. No complete manifest replay was repeated.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `PreweightedApplyGroups` | 1.504 | 3004136 | 2 |
| `PreweightedWrapperModel` | 1.656 | 3008544 | 1 |
| `PreweightedWrapperSemantic` | 2.082 | 4046620 | 1 |
| `SelectorValueLanePackScale` | 1.366 | 2990900 | 1 |
