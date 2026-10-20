# S4 actual scalar and limb arithmetic closure (focused v1)

This source-only packet records four focused green Lean results against the
current `fast_dots::four_dots` generated owner: successful scalar parsing gives
a canonical M31 scalar; the actual wide-to-limbs conversion/read exposes the
eight coordinate bounds; a successful actual inner limb body computes its
widened U32 product and checked U64 sum with the corresponding Nat values; and
the successor theorem additionally exposes the exact successful array update
and output-array equality. The inner arithmetic step retains its real current
body and explicit operation bundle. It assumes the consumed scalar/coordinate
bounds and a prefix bound of `3 * (2147483646)^2` for each old sum.

The green source files and exact source/object pins are listed in
`manifest.json`. Each attempt folder retains the original NUC command,
preflight, receipt, Lean output, and `/usr/bin/time` log. No compiled objects
are included. The imported generated `Types`/`FunsOpsV4`, parser, wide-to-limbs,
reducer, and Aeneas range owners are copied under `sources/owners/` so this
packet does not depend on mutable `/tmp` source paths. Their selected OLean
hashes remain those recorded in the original preflights.

The source revision anchor is the S4 research base `fa894d83d` and exact
current `four_dots` source pins in the already-frozen S4 extraction checkpoint
(`../s4-current-repin-20261020/checkpoint-v3/manifest.json`, committed S4 source owner `4b19b8384`; the current frozen bytes are identical). This packet does
not claim the source loop invariant or the seven-batch reducer composition.
A generic `Array.set` bound-advancement lemma is now green in the separate
`s4-current-prefix-array-set-bound-v1` addendum, but deriving the loop
invariant that supplies its per-cell input bound remains open. Whole
`four_dots` arithmetic closure remains open.

All four focused proof receipts report exit 0, swap 0, and standard-only
axioms `[propext, Classical.choice, Quot.sound]`. The exact elapsed time, peak
process RSS, and cgroup peak are in their per-attempt `receipt.json` files.
