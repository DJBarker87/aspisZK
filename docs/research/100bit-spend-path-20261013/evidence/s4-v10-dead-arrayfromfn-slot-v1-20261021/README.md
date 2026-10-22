# V10 candidate dead arrayFromFn slot

PROVED that changing only `FourDotsOps.arrayFromFn` does not change V10 `literalV10Helper` or the four-call `literalV10Outer`. The source body uses explicit eight-word initialization/reductions and indexed updates; it does not call this operation slot. This applies to the V10 candidate only.

The Lean target completed successfully with only standard axioms. This packet stores source and receipts only; it contains no `.olean` files. Direct import source/object pins and resolution positions are recorded. Recursive dependency provenance is inherited from the referenced producer packets and is explicitly marked incomplete here.

Original frozen source `from_fn` is a separate boundary and remains open; this theorem does not discharge it. Caller input validity remains upstream S1/S2.
