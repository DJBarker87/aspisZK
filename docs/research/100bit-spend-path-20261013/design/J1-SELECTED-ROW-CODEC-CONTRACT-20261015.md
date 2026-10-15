# Selected row byte-model contract

Continuation of J1.R4 on base `764bf20a6`. These strict codecs are model
interfaces. Their inverse and length theorems do not prove source execution,
accepted-proof soundness, or correctness of the later algebraic views.

Rows 0–24 reuse `SemanticRecordCodec` and `SemanticPayloadView`.
`SelectedSemanticMessages` embeds their exact encodings in the selected
bounded carrier. Successful typed decoding determines the entire message.
The C2 recovery callback remains explicit and must be justified at its
commitment cut by the compiler proof.

The selected `r1_wire` row 25 has 116 low-field values, not the older
`semantic_wire` layout's 87. Its first 87 values are three point-major
blocks of 29 claims; its last 29 values are the extra block. Row 26 has 29
low-field values. `CircleRecordCodec` retains each of these blocks, using
tag 4 / payload length 3712 for row 25 and tag 5 / payload length 928 for
row 26. A low-field value is a canonical 32-byte WideExact encoding with
zero upper QM31 coordinate. The extra block must remain available to the
six-functional-row view; using only the old three-point view is insufficient.

Opening rows use a different record frame: four little-endian length bytes
followed by the payload, with no semantic-record tag. The row's absorb label
is still supplied separately by the duplex. `LengthFrameCodec` describes
this exact byte shape. `OpeningRecordCodec` implements the following
lead-fixed payload and record statements:

| Global row | Typed payload | Payload bytes | Encoded message bytes |
|---|---|---:|---:|
| 27 | 29 low-field values | 928 | 932 |
| 28 | one full WideExact value | 32 | 36 |
| 29 | seven full WideExact coefficients | 224 | 228 |
| 30 | one 32-byte root and seven full WideExact coefficients | 256 | 260 |
| 31 | 64 full WideExact coefficients | 2048 | 2052 |
| 32 | empty | 0 | 4 |

Each row parser enforces its entire frame, strict element codecs, and
no trailing bytes. The checked inverse statements are `decode (encode x) =
some x` and `decode bs = some x → encode x = bs`. Model lengths must fit
`SelectedTranscriptParams.D = 3717`, as proved by `encode_length_le`.
The generic sequence operations reuse
`SelectedFieldSequenceCodec`, which is proved symbolically for arbitrary
length and does not normalize large concrete recurrences.

The row-30 root codec does not recover its word or justify commitment-time
stability. Row 31 fixes the final polynomial before query sampling, and row
32 has no payload; its ordered queries come from the preceding sampler
output. These byte shapes alone do not establish the causal parsers, the
round comparisons, or the accepted-query equations used by J5/J6.

Source pins and hash input sizes are in
`J1-SOURCE-CONFIGURATION-20261015.md` and
`J1-HASH-INPUT-LENGTH-INVENTORY-20261015.md`. The total absorb length is 34
plus the encoded message length, so the table is consistent with the
inventoried opening hash inputs 966, 70, 262, 294, 2086, and 38 bytes.
