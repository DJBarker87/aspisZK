# Actual QM31 multiplication focused source cut

This packet records attempt19, a focused Charon/Aeneas extraction rooted at the actual `field::QM31::mul` implementation. The only Rust reachability shim is `focused_qm31_mul`; the pinned `field.rs` and `wide_exact.rs` files are unchanged. The exact QM31/CM31/M31 arithmetic and reducer declarations reachable from QM31 multiplication are transparent in emitted Aeneas Lean. The four selected `WideExact` methods remain opaque.

This is an extraction and source-cut result, not a Lean refinement theorem or binary/runtime claim. The raw LLBC is intentionally omitted; `llbc-summary.json` records its SHA-256, declaration counts, and a compact relevant-function summary, while the Charon and Aeneas receipts independently bind that LLBC hash. Generated `Types.lean` and `Funs.lean` are source files only; no `.olean`, `.ilean`, or LLBC artifact is included.

The pinned sourcecut is `input/src/field.rs` (SHA-256 `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea`) and `input/src/field/wide_exact.rs` (SHA-256 `6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b`). Tool hashes, selector arguments, admission records, commands, environment, timing, cgroup metrics, and generated source hashes are preserved in this packet. The compilation target was the selected nightly `2026-06-01`; the source files are the pinned project checkout snapshots.

`python3 check_packet.py` validates packet hashes, source pins, successful zero-swap receipts, the exact start/opacity selectors, required transparent Aeneas declarations, and exclusion of raw LLBC and compiled Lean objects.
