# Circle record codec evidence

This package preserves the focused `R1CircleRecordCodec` attempt and its direct imported cache objects. The green run used the pinned Lean runner with `MemoryHigh=4G`, `MemoryMax=6G`, and swap disabled. It exited 0 in 1.66 seconds at 3,571,352 KiB peak RSS; the seven printed declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The byte model covers row 25 as 116 strict low-field values (87 point claims followed by 29 retained extras), and row 26 as 29 strict low-field values. It proves the framed sequence codec identities and decoded-message uniqueness. It does not prove an algebraic opening-view interpretation or correspondence with a Rust parser.

`source-manifest.json` records the source/base revision, source and object hashes, imported source pins, runner pins, exact attempt receipt paths, and archive members. Final objects are retained in the deterministic archive; no loose `.olean` files are included.
