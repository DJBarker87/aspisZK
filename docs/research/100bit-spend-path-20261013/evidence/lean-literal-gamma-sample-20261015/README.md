# Literal row-27 gamma sampler evidence

This bundle preserves failed attempt a and green attempt b for `R1LiteralGammaSample`. The theorem states that for a valid literal message at row 27, evaluating the byte-address sampler yields an ordinary challenge with nonzero gamma, using the selected row-27 sampler model. It does not establish transcript/source correspondence, terminal acceptance, or a security conclusion.

The final axiom audit for `valid_row27_nonzero` reports `[propext, Classical.choice, Quot.sound]`. The green focused compile took 1.57 seconds, used 3,598,288 KiB peak RSS, and reported zero swap under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. The bundle includes the final target object, direct import source/object pins, exact attempts, and pinned runner files.

Base source revision: `b400d586a84383b19f6250c383d56db1dda0a622`.

Loose object copies have been checked byte-for-byte against the matching archived members and moved outside the bundle to `/tmp/aspis-r1-retained-loose-objects-20261015/`; the compressed object archive remains the bundle’s canonical object artifact.
