# R499 chunks constructor arithmetic

This is an arithmetic-only milestone. It proves, for arbitrary `Usize n,k`
with `0 < k`, that remainder succeeds, `wrapping_sub n remainder` gives the
nonnegative prefix, and the quotient/remainder partition and remainder bound
hold. It also proves that the selected chunk sizes 4 and 16 are positive.

The final focused target is preserved in `focus-records/` under timestamp
`1791049853324485000`: exit 0, wall 0:01.12, peak RSS 2,537,732 KiB, zero
swaps. Its three complete axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. It imports the existing R489 arithmetic
dependency, copied here with SHA-256
`ac6766da5acfc45ac29bfe3c00d927a495b2104c08b87f745356de1f77da04d5`.

`focus-records/` also preserves the two changed-target failures named in the
initial worker receipt, the worker's initial green result
`1791049163869983000`, and the lead's normalized multiplication replacement
failure `1791049785987321000`. The latter receipt records its rejected
`sorryAx`-bearing intermediate axiom output; it is retained as failure
evidence only.

## Boundary

This does not prove an actual `ChunksExact` constructor body, native
allocation, `split_at_unchecked`, iterator behavior, or caller-frame behavior.
R495's existing capture identifies the surrounding constructor context by the
captured `chunks_exact` IDs 4 and 8, with iterator `next` IDs 10 and 12; those
are context references only and are not included in this arithmetic proof.
