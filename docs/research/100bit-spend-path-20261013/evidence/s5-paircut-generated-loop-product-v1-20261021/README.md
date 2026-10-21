# S5 generated PairCut loop/product source-only packet

This packet freezes three green Lean 4.32 targets: the generated PairCut body
equals the explicit range model in every branch, the whole generated loop
equals the model run, and a successful generated loop returns the decoded
indexed product sum with the read/push trace retained.

`extractor/extraction/generated/AspisR1WeightsPairCut/Funs.lean` is the retained
v23 Aeneas output. Its `weights.push_byte_products_loop.body` and
`weights.push_byte_products_loop` declarations are byte-identical to the
corresponding declarations in `generated-runtime/original/Funs.lean`. The
checker verifies both slices. The Rust input snapshot and source-pins record
the frozen weights source SHA; the v23 extraction packet classifies the wider
PairCut extraction as candidate-only.

The compiled runtime adapter is explicit. In `Funs.lean`, only
`WideExact.from_le_bytes` is redirected to the selected strict decoder. In
`FunsExternal.lean`, the EbyK `new`, `push`, and `finish` stubs are removed and
the already-checked `sourceOps` instance is installed. The checker verifies
these exact edits. The compiled `Types` object is separately pinned to its
selected source snapshot; it is not silently identified with the raw v23
generated Types source. The selected reader's extraction source, harness,
operation-order checker, and producer receipt are retained under
`reader-extraction/`. That checker validates the `weights.field` checked
offset, slice-index, strict-decode, and unwrap order against the selected
decoder-parameterized callback.

The enclosing PairCut extraction is still candidate-only. The retained v23
Charon/Aeneas run used a normalized harness; its balanced-span audit records a
different Pair method body, with inner loops factored into helpers and array
equality rewritten fieldwise, and explicitly marks equivalence unproved. The
exact generated `push_byte_products_loop.body` and `push_byte_products_loop`
declarations are byte-identical across the v23 extraction, the separate
transparent-reader extraction, and the runtime source used in these Lean
proofs. That local identity does not promote the whole Pair parent to an
unchanged-source extraction.

The Lean results prove equality and product meaning inside this generated
runtime model. They do not prove Rust-to-Aeneas extraction equivalence, Rust
standard-library iterator/runtime effects, or the runtime ABI for the decoder
and selected EbyK operations. The source snapshots, prior extraction receipt,
reader source adapter, and EbyK operation packet are included or pinned so the
remaining boundary is concrete and reviewable. No Rust source was edited.

The packet is source-only: it contains no `.olean`, `.ilean`, or `.llbc`
objects. `check_packet.py` validates source/object receipts, the targeted
generated-body and reader identities, the exact runtime patch, the normalized
parent disclosure, and the packet file hashes.
