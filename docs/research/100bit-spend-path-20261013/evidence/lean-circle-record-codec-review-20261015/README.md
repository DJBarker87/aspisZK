# CircleRecordCodec independent audit

The CircleRecordCodec bundle passes its checksum list. The final source, attempt snapshot, receipt and sidecar match; the current worktree source matches the green hash. The three direct-import source pins and archived objects match, as do all runner pins and archive member hashes/sizes. The green run exited 0 in 1.66 s at 3,571,352 KiB RSS, zero swap, under 4G/6G/0. Its seven axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

The model has 116 low-field values in row 25 (tag 4, 3,712-byte payload, 3,717-byte tagged frame), retaining the first 87 point-claim values and final 29 extra values. Row 26 has 29 low-field values (tag 5, 928-byte payload, 933-byte frame). This matches the cited `r1_wire` row shape and the `r1_semantic` offset 87 syntactically. It does not establish Rust parser or semantic correspondence. The separate `semantic_wire` row-25 layout remains 2,784 bytes and is not conflated with the S2 `r1_wire` layout.

The inspected `LengthFrameCodec` is a distinct tagless model with a four-byte little-endian length prefix. `Transcript.absorb` frames opening payloads with that four-byte length after state and row bytes, without the semantic P1 tag. `LengthFrameCodec` was not included in this CircleRecordCodec compiled bundle; this review makes no claim about its build provenance.
