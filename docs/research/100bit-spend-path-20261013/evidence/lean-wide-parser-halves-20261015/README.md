# Wide parser array halves

This focused Lean module defines the two checked 16-byte segments of a 32-byte Aeneas array, maps the original array into retained bytes, and proves each half agrees with the corresponding 16-byte decoder view. The slice equalities reuse `ParserArraySlice.slice_segment`; the byte-order equalities are pointwise. No parser-canonicality premise is used.

The exact source compiled is `WideParserArrayHalves.final.lean` (also linked from the research Lean directory). Attempt `array-halves-a` failed during elaboration because `Byte` was ambiguous and the lambda index types were implicit; its exact source, receipt, and log are retained. Attempt `array-halves-b` succeeded after adding explicit type annotations. It ran on the pinned 4G/6G/swap-zero cgroup: 1.85s, peak RSS 3,783,092 KiB, zero swap. Its four axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

`source-manifest.json` records the source base, imported source hashes, and both attempt artifacts. `runner/` contains the pinned wrapper and environment snapshot.
