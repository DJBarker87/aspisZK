# Owned field reader: bounded checked/wrapping index bridge

The Lean bridge proves that, for an explicit `i.val < 48` bound, the owned
reader's wrapping byte-offset operations agree with the checked Usize
operations used by the generic `WeightsFieldExplicitDecoder` body. It then
reuses the existing checked-slice decoder theorem to retain the same selected
slice and decode result.

The bound is an input to this theorem. This packet does not prove that an
actual caller supplies `i.val < 48`, nor does it claim source-to-runtime or
binary refinement. The reused R152 arithmetic module is included as a
source/receipt/profile reference; its `.olean` is not included.

The main target compiled with Lean 4.32, exit status 0, in 22.754 seconds at
2,112,563,584 bytes aggregate peak RSS with zero swaps. The four audited
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Run `python3 -B check_packet.py` to validate source, receipt, selected direct
import pins, axiom reports, and the reused R152 dependency receipt.
