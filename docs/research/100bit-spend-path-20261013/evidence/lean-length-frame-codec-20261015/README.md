# Tagless length frame codec evidence

This bundle preserves the focused `R1LengthFrameCodec` compile and its direct imported cache object. The run exited 0 in 0.88 seconds at 1,808,836 KiB peak RSS, with `MemoryHigh=4G`, `MemoryMax=6G`, and swap disabled. All four printed declarations depend only on `propext` and `Quot.sound`.

The modeled frame is exactly `lengthBytes payload.length ++ payload`: a four-byte little-endian length prefix with no tag. The module proves frame length, successful parsing of an encoded frame, parse soundness, and an iff characterization. It is a byte-model codec only and does not establish a Rust parser refinement.

`source-manifest.json` records the base revision, hashes, direct import source/object, runner pins, attempt artifacts, and deterministic object archive. No loose `.olean` files are retained.
