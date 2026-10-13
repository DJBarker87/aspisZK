# TwoRoundComparison focused Lean receipt

Target `R1TwoRoundComparison`, source `lean/TwoRoundComparison.lean` SHA-256
`781f9d979760e55cdade84ddf597f226ca2f7f9a44ed3dfd1189a27640f3933e`.
Base worktree revision `31b6f19270a3e6463a2a4d92a058042cdf95cdce`, plus this
uncommitted source. The NUC command was
`./run2.sh two-round-comparison-r1-20261013a R1TwoRoundComparison 5000 6`.

The focused run exited 0 in 0.93 seconds, maximum RSS 2,069,564 KiB,
zero swaps, using MemoryHigh=4 GiB, MemoryMax=6 GiB, MemorySwapMax=0,
and Lean `-M5000`. The external 24 GiB reservation was included before
launch. Cached environment manifest SHA-256:
`ad7b87bbcfd84dc762927729c3d35a1822a530e57538a58c9d559f6ec4b6754e`;
Lean revision `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

The first three printed theorems use `[propext, Classical.choice, Quot.sound]`;
the fourth uses `[propext, Quot.sound]`. No `sorryAx`. The one unused-section-
variable warning is not a proof failure. The exact output, source hash and
`/usr/bin/time -v` receipts are retained here.

The theorem is conditional deterministic algebra and finite root counting.
It does not prove candidate extraction, concrete source semantics, prefix
causality, sampling laws or the Fiat--Shamir reduction.
