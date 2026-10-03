# R527 selected parts arithmetic bounds

The existing `partsN` definition maps four coordinates bounded by m into nine entries bounded by m. Pairwise products of those entries are bounded by m². The strengthened final theorem also shows that strict input-coordinate bounds below p imply all nine selected parts are strictly below p.

Target `AspisR515SharedGamma/R527PartsBounds.lean`; source revision `894244dd2acf16b977a855b015e19beb1b42905d`; source SHA-256 `fdc2044cd17ea115d20c49fe537167c205244da0c4c5c1652a3ff2df39597cc7`. Run `1791056025745213000` exited 0 in 1.45 s; peak Lean-child RSS 3,242,456 KiB; swap 0. Pinned Lean 4.32, `-j1 -M4500`, MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. All three complete axiom reports contain only `[propext, Classical.choice, Quot.sound]`.

This is not a source decode or execution theorem. It does not prove correction coverage or end-to-end privacy/security.

First remaining source proposition: the actual selected group and outer loops use these canonical entries and realize the grouped gamma arithmetic, including each checked failure and transcript/caller boundary.
