# Installed S4 QM31 parser source bridge

This focused Lean result proves that the concrete installed `qm31FromBytes` slot is, for every slice and every result branch, the transparent retained `AspisR1DecodeKFullV10` QM31 decoder followed by the checked coordinate map into the Current carrier. On a typed 16-byte frame it equals the retained strict decoder, including rejection (`none`) of noncanonical coordinates.

Both theorems use only `[propext, Classical.choice, Quot.sound]`. The output capture for this first successful compile lost peak RSS, swap, and source revision. Those fields are recorded as unknown; no unchanged rerun was made.

The V10 minimal-fixed-calls external template declares a separate axiom for `QM31.from_le_bytes`; this packet makes no claim about that axiom-bearing declaration. The bridge instead pins the actual transparent generated DecodeK body. Variable-length slice framing, Rust `from_fn` semantics, the full caller, and final S4 re-pin remain open.

Run `python3 check_packet.py` to verify source, object, compiler, direct-owner hashes and axiom output.
