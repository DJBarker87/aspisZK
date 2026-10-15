# Literal matching facts evidence

This bundle preserves attempts a and b for `R1LiteralMatchingFacts`. Attempt a failed during proof elaboration; attempt b is the final successful focused compile. The theorem decomposes a successful literal matching-data read into the successful component reads used to construct its result. It establishes no acceptance, source correspondence, or security claim.

The final audit reports `[propext, Classical.choice, Quot.sound]` for `AspisR1.LiteralMatchingFacts.read_success_components`. Both attempts were run with the pinned NUC wrapper under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`; receipts record elapsed time and peak RSS. The archive contains the final target object and its direct import object.

Base source revision: `b400d586a84383b19f6250c383d56db1dda0a622`.

Loose object copies have been checked byte-for-byte against the matching archived members and moved outside the bundle to `/tmp/aspis-r1-retained-loose-objects-20261015/`; the compressed object archive remains the bundle’s canonical object artifact.
