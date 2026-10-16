# Complete extracted mask formula

The selected-mask caller now has a checked execution-and-formula theorem on
Lean 4.32. Given canonical source inputs, it succeeds and returns a canonical
value equal to the intended local exact formula. Both coefficient-population
loops, their disjoint schedules, the zero coefficient at index 23, the linear
forms, polynomial evaluation, power and final arithmetic are composed.

[Evidence](../evidence/current-mask-full-formula-20261016/README.md) records
15 focused targets, 51 standard-only axiom reports and all failed attempts.
Peak target RSS is 3,144,004 KiB and process swaps are zero. Existing proofs
are reused; the loops and coefficient sums remain symbolic. One dependency
receipt's source field is explicitly reconciled against its actual imported
object and that object's successful producing receipt; the original evidence
and uncompiled draft remain preserved.

The next bridge maps this exact QM31 formula into the historical
`WideExact`/`R0P.Mask.maskValue` relation with an explicit ring homomorphism and
four basis-compatibility equations. It must not identify the two field carriers
by assertion. Canonicality of accepted inputs and the complete Rust acceptance
contract remain separate. Extraction, privacy and the remaining soundness and
runtime/settlement obligations are still open; this is not the full 100-bit
private-spend theorem.
