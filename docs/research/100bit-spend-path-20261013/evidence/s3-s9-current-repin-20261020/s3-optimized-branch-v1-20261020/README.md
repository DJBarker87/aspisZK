# S3 optimized inactive lookup bridge v1

This source-only packet checks the exact frozen S2 dispatch and table literals, then proves that each optimized table bit agrees with the emitted S2 `Variant::row(16*j+s)` followed by the extracted `opening::inactive` helper. The optimized path uses its literal grouping tables rather than invoking `Variant::row` at runtime.

The source checker verifies the Rust tables and dispatch against the Lean model; the Lean theorem reuses the actual row/inactive output theorem and proves the finite table-cell identity. No production sources changed.

The local focused Lean 4.32.0 check exited 0 in 17.171 s, peak RSS 2,704,949,248 bytes, swap 0. `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. The compiled object remains in the recorded `/tmp` cache and is not included.

The packet does not prove the grouped coefficient/subset-weight accumulation in `s2_grouped_inactive_pair`, nor the full optimized `Weights::pair` output.
