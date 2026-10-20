# EbyKDot constructor source cut (v1)

This packet records the exact extracted constructor path `canonical::Dot::new` → `EbyKDot::new` and public typed entry `new_entry`. The Rust cut preserves these actual method bodies; the wrapper only exposes the return type to Charon/Aeneas. The Lean proof establishes both Dot accumulators contain four zero words and `count = 0`.

The source cut is an isolated extraction kit based on the frozen adopted source revision recorded in `source/input/source-pins.json`; it does not modify production Rust. Extraction and Lean adapter checkers are included. The only Lean source adaptation removes generated `set_option maxHeartbeats` and `set_option maxRecDepth` lines. No external template is imported. The proof uses standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

Scope evidence is in `extraction/evidence` and `lean/evidence`; Lean cgroup scope peaks and swap are recorded per receipt. Compiled OLean files and LLBC binaries are intentionally excluded; their hashes appear in the receipts.

This closes construction only. `EbyKDot::push`/finish arithmetic, the 4096-term overflow bound, and finish-caller integration remain open.
