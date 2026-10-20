# S4 four-dots fixed-call candidate v6

This isolated candidate tests whether the current `fast_dots::four_dots` cone becomes extractable with explicit fixed calls and fixed-size arithmetic loops. It is not a production edit and does not establish equivalence to the original `core::array::from_fn` Rust semantics.

The candidate moves the existing single-slot closure body into `four_dots_one`, then `four_dots_fixed` performs the existing 608-byte slice conversion and calls the helper sequentially with slots 0, 1, 2, and 3, returning those four results in order. In v6 the two inner eight-limb loops, the two-step tail push loop, and the eight-coordinate reduction array are written explicitly. The fixed wrapper body is checked against the generated Lean body by `check_fixed_calls.py`; helper bytes are pinned by the Rust file SHA. The checker confirms no `from_fn` remains in the helper or generated Funs module.

The Lean theorem `successful_call_trace` proves success of the abstract fixed-call sequence implies success of each helper invocation in order and the exact returned array. It is a call-flow adapter; it does not yet connect the helper to the emitted arithmetic model, prove original `from_fn` equivalence, or close the existing S4 seven-batch arithmetic invariant for this new generated owner. Those remain open.

## Extraction receipts

The exact Charon and Aeneas commands, receipts, timing logs, and source pins are in `evidence/v6/`. Charon and Aeneas both exited 0 using the cached release tools under `MemoryHigh=2GiB`, `MemoryMax=4GiB`, `MemorySwapMax=0`; no OOM or swap occurred. LLBC is identified by hash only and is intentionally not included.

## Lean receipt

The focused local Lean 4.32 compile emitted `lean.log` and `lean-time.log`. It compiled only `FourDotsFixedCallTraceV1.lean` with `-j1 -M4400`, import `Aeneas`, and the recorded cache roots. `#print axioms successful_call_trace` reports `[propext, Classical.choice, Quot.sound]`. No external generated template was imported.
