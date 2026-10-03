# R435: counted-fold helper guard fragments

R435 proves the scalar overflow guard and modeled pointer-order guard needed for the captured counted fold. These are library/fragment facts with explicit representation boundaries. They do not prove native helper, pointer, or whole-fold execution, nor privacy or soundness.

## Focused verification

Exact target: `AspisV8R19/R435HelperGuards.lean`. Promoted source is successful attempt C, SHA256 `c88ced1006c9abcf5ed2fac0945737906c3adcadccf6432843c6272149f729bd`, source revision `51f7e12388958a5e565273359022df04bef49bff`.

| Attempt | Result | Wall | GNU peak RSS | Swap |
| --- | --- | --- | --- | --- |
| A | exit1: platform-size simplification failed | 1.05 s | 2,525,168 KiB | 0 |
| B | exit0: four guard reports | 1.09 s | 2,540,672 KiB | 0 |
| C | exit0: adds bounded addresses and pointer fragment success | 1.32 s | 2,540,244 KiB | 0 |

A's failed output includes `sorryAx` and is rejected history. B fixes the proof by using Lean’s supported platform-size cases, 32 and 64, rather than assuming a size equality. C adds a new bounded-address theorem from the existing allocation no-wrap property and slice bound; it is not a rerun of unchanged B. Successful sources, commands, errors, metrics and complete logs are retained. C’s six complete `#print axioms` reports contain only `propext`, `Classical.choice` and `Quot.sound`. Its unused-simp-argument warnings are retained; no successful source edit was made merely to rerun those warnings.

All focused jobs use pinned Lean4.32.0 commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, the cached workspace, `lake env lean -j1 -M4500`, MemoryHigh5 GiB, MemoryMax7 GiB, MemorySwapMax0, TasksMax128. C’s terminal cgroup peak is 303,529,984 bytes, swap peak0, no OOM/high/max events. GNU and cgroup metrics remain separate; their difference is unexplained. Source and copy receipts, complete axiom reports, independent custody checks and the lead audit are saved.

## Precisely proved boundary

`helper115Overflow` uses the Aeneas usize-to-u64 casts and `UScalar.overflowing_add` tuple flag. `cast_usize_u64_value` proves that supported platform usize values survive that cast. For `i.val < len.val`, `helper115_no_overflow` combines the existing R195 successor bound with the u64 overflowing-add specification to prove the flag is false. This is a new guard connection, not a repeated proof of R195.

`helper115Fragment` takes an arbitrary rejected-guard result. Its successful result is independent of that value under the bound. This expresses that the rejected continuation is unreachable within the fragment; it does not invent or equate a Rust panic/abort/failure implementation.

The pointer theorem establishes address order in the R432 backing-allocation representation. The bounded-address theorem additionally proves that both range endpoints fit below 2^64 when the range is bounded by the allocation's cell length. The order fragment returns success for those endpoints. Unbounded natural-number address order alone is not asserted to imply legal native pointer arithmetic; the saved theorem boundary preserves the source validity/provenance gap.

R434 preserves the complete native helper bodies. The six source-shape checks identify helper114’s `Ge`, helper115’s two Usize-to-U64 casts, `AddChecked`, tuple field1, the false-flag early return and the separate full failure tail. These are structural checks of the frozen capture, not a kernel proof that native AddChecked equals the Aeneas overflowing-add primitive or that native pointer comparison equals modeled address comparison. The small fragment definitions were inspected separately by the lead. The full panic/message/abort and unwind paths remain in R434; their semantics is not replaced by the fragment parameter.

## First remaining proposition

Justify the native primitive/value-image correspondences, then prove the actual fold invariant supplies the slice bound and `i < len` at every indexed read and unchecked successor. Bind the exact mutable FnMut borrow, restoration of captured power, source slice-storage frame, native callback dispatch and complete drop/unwind/error behavior. R432/R433/R435 remain components of this bridge, not its conclusion. Vec::extend and whole callback/oracle chronology remain open.

Universal joint C1/H1/G compatibility, the entire published-view simulator with shared-oracle probability losses, coherent original quotient-pair extraction before beta and optimized-to-source acceptance remain unproved. Genuine 999,790 / 999,532 CU and all security parameters are unchanged. No benchmark, unchanged regression, deployment, merge, transaction or wallet operation occurred.
