# R384: positive-transfer delta degree fragment

R384 proves a degree bound for a declared exact-field polynomial representing the selected positive-transfer scalar contribution. The model residual `p0col1 * p1col1 * p0col3 - 1` has degree at most 12. The fixed row-1014 selector contributes degree at most 1, the point-equality factor contributes at most 1, and the declared scalar coefficient is constant. Their product therefore has degree at most 14 in the selected coordinate.

The promoted source is [R384PositiveDeltaDegree.lean](lean/AspisV8R19/R384PositiveDeltaDegree.lean). It imports the exact R381 source snapshot recorded in the evidence bundle. The successful focused run exited 0 in 6.69 seconds, with 2,933,904 KiB peak Lean-child RSS and no swap. All three complete `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The earlier failed draft is preserved with its source, log, and receipt; it failed while simplifying the fixed row-selector degree proof and its interim `sorryAx` reports are not successful evidence.

The first remaining proposition is to prove that the selected positive-transfer source expression, including field-word packing and iteration, corresponds to this declared polynomial. R384 does not prove that source correspondence, the complete terminal degree, correction existence, universal coverage, privacy, or security.
