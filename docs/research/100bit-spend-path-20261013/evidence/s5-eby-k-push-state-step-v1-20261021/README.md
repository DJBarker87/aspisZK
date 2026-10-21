# EbyK push state-step proof

This focused Lean target proves a one-step invariant for the same returned state: successful valid-scalar EbyK push preserves both count-indexed sums bounds, increments its count by one, and updates both decoded sums by the actual QRaw products.

The caller premises and the source-model / Rust Std correspondence boundary are recorded in `manifest.json`. Run `python3 check_packet.py` from this directory to validate frozen source and receipt hashes. No OLean binaries are included.
