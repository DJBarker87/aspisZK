# Opening record codec focused evidence

This bundle records the focused compile of `AspisR1.OpeningRecordCodec` for selected rows 27–32. The checked model has exact payload sizes 928, 32, 224, 256, 2048, and 0 bytes; it composes the strict low/wide sequence codecs, the row-30 state-plus-seven-wide layout, and the four-byte length frame. The result is bounded by the selected 3717-byte message carrier.

Attempt a is preserved as a failed proof-plumbing draft. It emitted eight axiom reports, all eight containing `sorryAx`; this is retained diagnostic provenance and is not a successful audit. Attempt b is the final green focused compile: exit 0, 2.18 s, peak RSS 3,580,928 KiB, swap 0 under 4G/6G/0/128. Its eight reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The strict byte-model inverse does not establish Rust parser refinement, commitment recovery, causal transcript checks, accepted-proof soundness, or a probability theorem. Direct import source/object pins and the pinned runner/environment are recorded in `source-manifest.json`; compiled objects are retained only in the deterministic archive.
