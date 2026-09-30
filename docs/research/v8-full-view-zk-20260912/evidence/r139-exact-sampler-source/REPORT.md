# R139 exact sampler source report

The exact extracted R137 `challenge_qm31` is now connected to the established
source-shaped sampler program through its actual wrapping indices, rejection
loops, mutable limb writes, source squeeze and state advance.  The actual
nonzero wrapper is also finitely unfolded for its three attempts.

All nine focused targets exited 0, used zero swap, and stayed below 3.72 GiB
peak RSS.  The final release target exited 0 in 1.58 seconds at 3,693,124 KiB
peak RSS.  Printed axioms contain no `sorryAx`.

This evidence does not claim the nonzero recurrence/model correspondence,
callback chronology, shared-oracle distribution, privacy or soundness.
