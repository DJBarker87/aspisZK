# Record frame codec focused evidence

This bundle preserves the focused Lean target for a five-byte tagged, little-endian length-prefixed record model. The parser checks exact framing bytes and payload size. It does **not** establish equivalence to Rust `u32` conversion or Rust parser error behavior.

Source base: `8e6c2b4cba1c54fe165f7436f5fc3ada1e1ae0f3`. Target: `R1RecordFrameCodec`. Attempts a and b are preserved with exact snapshots, receipts, logs, time logs, and hash sidecars; a failed during proof plumbing and b is green.

The green result used a 4 GiB memory high limit, 6 GiB maximum, zero swap, and 128 task cap. Receipt b records exit 0, 1.06 seconds, and peak RSS 1,807,312 KiB. Six audited declarations report `[propext, Quot.sound]`. The object archive contains only the final target object. The imported `R1PublicInitFrame` source and object hash are pinned in `source-manifest.json`. Runner and environment pins are retained.
