# Aeneas reverse-iterator / current-polynomial consumer (V8)

This result joins the separately frozen Aeneas-only actual `Rev.next` loop
refinement with the checked current-Wide seven-bind polynomial port. For the
fixed range `[0,7)`, the Aeneas loop produces the same `Result E` as the
current unrolled polynomial for every input byte slice and challenge `x`. The
callback is the actual ordered current-Wide step: multiply the accumulator by
`x`, decode the coefficient with `currentRecordFieldLookupNat`, then add it.
Thus failure and divergence behavior are included in the equality; no
independent coefficient-success or canonicality assumptions are introduced.

The Rust standard-library correspondence remains open: the Lean loop follows
Aeneas's concrete `Rev.next` and `Range.next_back` bodies, but this theorem does
not itself prove Rust `Rev::fold` is emitted as this loop. The direct imported
owners are the checked Aeneas actual-loop theorem, the current unrolled
polynomial module, and its current reverse-range model. No generated protocol
`Funs`, `FunsExternal`, or `TypesExternal` owner is imported.

The successful NUC attempt used Lean 4.32.0 with `-j1 -M 4400`; cgroup
`MemoryHigh=1GiB`, `MemoryMax=2GiB`, `MemorySwapMax=0`. Exit 0, wall 2.307s,
process peak RSS 3,693,484 KiB, cgroup peak 375,681,024 bytes, process-scope
swap 0, and no memory events. Axiom reports for the actual-loop equality,
loop-to-range equality, and success iff theorem are all
`[propext, Classical.choice, Quot.sound]`.
