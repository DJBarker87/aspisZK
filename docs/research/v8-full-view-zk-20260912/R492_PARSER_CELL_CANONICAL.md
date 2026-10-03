# R492 parser cell canonicality

`lean/AspisV8R19/R492ParserCellCanonical.lean` was compiled successfully in
the pinned cached Lean workspace. The promoted canonical file is byte-identical
to the final source snapshot, SHA-256
`ab5066ac4caec99815aa578e45dff779059479ab870815c1aa63cb2d598d9eb8`.

The final run was target `AspisV8R19/R492ParserCellCanonical.lean`, source
revision `d1d92d62a244732bc9ecf742e79fc05c7229ac5b`, exit 0, wall time 0:01.55,
peak Lean-child RSS 3,713,628 KiB, and zero swaps. It used `-j1 -M4500` in a
systemd user scope with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and
`TasksMax=128`. Its complete nine `#print axioms` reports are in the raw final
log. They contain only the standard `propext`, `Classical.choice`, and
`Quot.sound` dependencies where present; `canonicalPacked`, `lanes`, and
`canonicalQM31` report no axioms.

The proved boundary is arbitrary packed-cell lists: the parser mask accepts
exactly when all four raw coordinates per cell are below `P`, and packed-word
decoding has the corresponding canonicality equivalence. It does not prove
native parser construction, iteration, alignment, allocation, or
error/result correspondence.

The first remaining proposition is the actual helper-lowering/source bridge,
followed by the complete parser ordered image. Evidence, including the initial
worker success, the lead duplicate-declaration failure, and the final green
run, is in `evidence/r492-parser-cell-canonical/`.
