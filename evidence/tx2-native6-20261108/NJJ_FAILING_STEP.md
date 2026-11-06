# Failed shapes retained

NJJ_K015: pending_step, width64 arbitrary raw plus weight vectors, timed out inside CBMC at the unchanged90s limit (scope wall95.477s, peak3155824KiB, swaps0). No credit. It was not rerun. Replacement: pending_window, one4-word destination row and source K at an arbitrary source index, plus NJJ_Cuts / existing Port3_NativePendingLoop frame and finite induction. No cap or timeout change. NJJ_K016 is reserved for a genuinely different shape, not a negative control for a nonexistent passing K015.

K001–004 are pre-proof input/compiler setup failures, repaired in NJJ_REPAIRS.md. Failed Lean attempts are retained; only final successfully compiled objects may be selected. No failed version with sorryAx may enter the combined audit.

NJJ_L009 exposed an avoidable fixture dependency through JGc_TX2_QueryDictionary (missing RawTx1DigestLog). The replacement directly constructs the concrete query record from already coherent primitive owners, without importing the fixture forest. No shared workspace/object repair.

NJJ_K025: value on full symbolic raw64 plus arbitrary index/frame timed out at90s (wall95.090s, peak3391240KiB, swaps0). Not rerun. Replacement value_window executes the actual value() on one selected row; NJJ_Value.projection derives that row from the arbitrary full-vector index and proves the complete source Result equal, rather than requiring a singleton caller. Existing full-U64 emitted reducer laws are reused. No timeout or cap increase.

NJJ_K080: the extra supplied-KMX guard did not run because cargo-kani could not match the requested KMX_ptr_wrong proof root. This is an invocation failure, not a failing fidelity control or a semantic verdict. The80-slot native budget is exhausted; it was not reissued under another kind/number/name. Every admitted local positive still has its own matched failing control; K080 adds no credit. No harness was renamed to change a verdict.
