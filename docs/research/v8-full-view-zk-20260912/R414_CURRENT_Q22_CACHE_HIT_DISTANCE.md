# R414 q22 cache-hit distance

The promoted theorem bounds the difference between lazy q22 and the uniform-candidate kernel by the explicit `guardFresh` hit-mass term for any bounded result observer. The challenge theorem specializes this comparison to eight blocks, with the 64-draw cap fixed from the empty scan state. Cached reads remain cached; no `FreshFrom` assumption is used.

The comparison is on the projected result, not full traces or transcript state. It gives no source-specific hit-mass bound or numerical security claim. The remaining bridge must bind actual initial state, adversary cache, callback, and retry chronology and bound the hit mass; normalized legal-query support also remains open.

See [R414Q22CacheHitDistance.lean](lean/AspisV8R19/R414Q22CacheHitDistance.lean) and [saved evidence](evidence/r414-q22-cache-hit-distance/README.md).
