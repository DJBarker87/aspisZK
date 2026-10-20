# S4 generic array-set prefix bound (focused addendum v1)

`set_advances_bound` proves the pointwise bookkeeping step needed for the
S4 inner-limb invariant. If every cell of an eight-entry `U64` array is at
most `k * cap` and the newly written value is at most `cap`, then after a
successful `Array.set`, every cell is at most `(k + 1) * cap`. The proof
splits only on whether the queried cell is the updated index and uses the
standard list-set readback lemmas.

The exact source, NUC admission snapshot, direct-import pins, command,
preflight, Lean output, timing log, and result receipt are included here.
There are no compiled objects. It was compiled under Lean 4.32.0 with
`-j1 -M 4400`, `MemoryHigh=1GiB`, `MemoryMax=2GiB`, and `MemorySwapMax=0`;
fresh admission passed with 32.375 GiB finite reservations and 9.067 GiB
uncapped working-set accounting. Exit status was 0, wall time 1.304 seconds,
peak process RSS 2,379,964 KiB, scope peak 288,993,280 bytes, and scope swap
0. `#print axioms` reports `[propext, Classical.choice, Quot.sound]`.

This is a generic state-update lemma only. It does not establish the premise
`hbase` for the actual four-term/eight-limb generated loop, does not prove
loop termination or iteration coverage, and does not itself close the
seven-batch arithmetic/reducer composition. See the separate current inner
body proofs in `s4-current-arithmetic-closure-v1`.
