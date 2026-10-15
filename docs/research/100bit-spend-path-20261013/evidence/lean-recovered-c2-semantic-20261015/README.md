# Recovered C2 semantic pair

This focused module repackages the two C2 coordinates as the matching semantic words. Its projections agree with lanes 26 and 27 of `TypedRecoveryContext.fullWords`; it also proves the existing `c2Words` and `c2Base` obligations for that pair. For six-level paths, a successful `decodeC2At` yields the corresponding pair projection at the indexed query slot.

The module consumes caller-supplied C2 packed leaves and paths. It adds no accepted-opening, source/refinement, causal-recovery, or protocol claim. Attempt a and b failed; attempt c is the final green source. All attempt snapshots, logs, time logs, and receipts are retained. Each public declaration has the standard axiom set `[propext, Classical.choice, Quot.sound]`.
