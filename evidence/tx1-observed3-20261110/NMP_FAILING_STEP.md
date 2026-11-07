# NMP failing steps

Target not yet established. No candidate root.

K018, ACTUAL prepare at original57607 arbitrary bytes, allocation-error arm,
retired after90s CBMC timeout (scope101.035s, RSS4128084KiB, swap0).
The shared check unnecessarily formed a symbolic read over the entire57607-byte
proof to test a frame even on this arm, where allocation fails before any proof
slice is passed to a child. This creates the large array-selection shape.
Never rerun this unchanged shape or raise its cap/timeout. Next: split the
functional Result/scratch/call-log obligation from the proof-buffer frame,
retaining the frame as an explicit obligation composed from returning child
frames and disjoint local-log writes. No credit for the timeout.

The initial archived Pool corpus also predates the owner amendment in15 files.
Prior selected verifier dependency graphs reach no aspis-pool. L016 restores
all20 Pool files to b936275465 in OWN scratch; the following install strengthens
the normalized frozen-body check from the five overlay bases to every frozen
file. The original archive and mismatch finding are retained.

K009 public-error137 whole frame shape also timed out90s (94.124s scope,
RSS1658792KiB,swap0). Retired. The replacement splits Result/call-log/typed
reply forwarding from the independent immutable-proof frame; its name includes
calllog because its claim differs. The original full frame statement is NOT
claimed by this replacement. K003 retains the parse-error input-byte frame
only; the other branches still need composed child frames and log disjointness.
No timeout/cap increase or unchanged shape rerun.
