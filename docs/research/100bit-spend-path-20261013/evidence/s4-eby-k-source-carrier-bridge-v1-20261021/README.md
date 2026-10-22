# S4 EbyKDot source-carrier bridge

This packet proves an invertible fieldwise mapping from the retained transparent generated `AspisR1EbyKFinish.EbyKDot` representation to the explicit `AspisR1EbyKPushCutV3.fast_pairing.EbyKDot` carrier used by the current S5 operation owners. The maps preserve both `canonical.Dot.sums` arrays and the `count` field. The Rust `canonical::Dot` and `EbyKDot` declarations are pinned by exact source byte slices from the same `fast_pairing.rs` revision and checked against the generated field order/types.

The result is a representation bridge only. It does not identify method implementations or prove source calls/operation semantics. Current `EbyKDot::new`, `push`, and `finish` operation laws remain supplied by their separately pinned S5 owners; enclosing S4 caller and source call-site refinement remain open. No generated Funs/Types external template is imported.

Run `python3 check_packet.py` from this directory to verify all file hashes, direct import producer pins, Rust source slices, Lean field declarations, and the captured focused compile receipt.
