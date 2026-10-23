# Concrete actual Pair in the finish slot

The Pair operation is now an explicit implementation instance: exact actual32 `Weights.pair`, with coordinate-only input/output and eight-error constructor transport. Existing outer finish success derives the same prefix operation and same actual native accepted call, rather than requiring a successful Pair callback. All allocation and actual Pair control flow are retained.

Other FinishOps operations remain explicit. In particular newWeights is not yet claimed to be the actual constructor, so self.S2 is not inferred merely from p.variant.S2. This packet does not claim complete finish arithmetic, whole runtime correspondence, allocator/primitive preservation or release soundness.

Validation: one focused target, standard axioms, zero swap, root serialized one-thread M4400 controller,7.5GiB aggregate stop,120s watchdog. Exact command/profile/source/revision/object receipts retained. No binary/full inventory or final release replay. Target not yet established.
