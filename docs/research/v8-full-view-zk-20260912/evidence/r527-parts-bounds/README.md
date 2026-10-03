# R527 selected parts bounds and canonical range

The final target proves (1) all nine entries of the existing `partsN` definition are ≤ m when each of four input coordinates is ≤ m, (2) each `productsN` entry is ≤ m² for two such inputs, and (3) each `partsN` entry is strictly below p when all four input coordinates are strictly below p. The lemmas preserve the existing `partsN` and `productsN` definitions; the final canonical range theorem reuses the bound and p=m+1. This is an arithmetic fact only, with no target-coverage premise or claim.

Final target `AspisR515SharedGamma/R527PartsBounds.lean`; source revision `894244dd2acf16b977a855b015e19beb1b42905d`; SHA-256 `fdc2044cd17ea115d20c49fe537167c205244da0c4c5c1652a3ff2df39597cc7`. Final run `1791056025745213000`: exit 0, wall 1.45 s, peak Lean-child RSS 3,242,456 KiB, swap 0; pinned Lean 4.32, `-j1 -M4500`, MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. All three complete axiom outputs contain only `[propext, Classical.choice, Quot.sound]`; the final run was warning-free.

All five focused attempt triples are preserved under `attempts/`: three initial failures, the first arithmetic green, and the final strengthened green. These statements do not prove the selected source-coordinate decode, prover execution correspondence, correction coverage, privacy, or security.
