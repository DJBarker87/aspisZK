# Actual digest decoder and source field-byte parser bridges

`LaneEncoderActualDigestDecoderSuccess` proves that the actual extracted `decode_digest_canonical` returns the eight supplied values when its eight actual canonical field-parser calls succeed on the same source byte chunks. The result preserves the actual Result/Option constructors and output array. The byte getter bridge identifies the source Array and Slice accesses without replacing the decoder by a different specification function.

The field-parser bridge connects the actual decoder's M31 parser to the existing canonical parser. Parser acceptance is derived for actual U32 little-endian encoder output under the explicit bound value < 2147483647. The final field-window theorem composes actual M31 byte encoding, exact output-window equalities, Array/Slice getter correspondence and parser acceptance. It retains canonicality as a premise rather than inferring canonicality from serialization success.

These are composable source execution results. At this checkpoint the complete digest encoder-to-decoder composition is still a separate theorem under focused verification; the decoder theorem itself retains its eight parser premises. Complete record decoding, production encoder loop/guard correspondence, and authenticated persistent account readback/custody/runtime remain separate. This packet does not establish complete verifier soundness or the final 100-bit security/privacy theorem.

Existing source byte-codec, chunk-equality and successful encoder chunk projections are reused. Production Rust and runtime artifacts are unchanged by this packet.

Validation: 6 focused targets; 6 standard-only axiom reports; zero process swap. Maximum RSS 3,812,036 KiB. Receipts record exact source/object/import hashes, command, base revision, wall time, RSS and cgroup cap. Repeated and internal import pins were checked for coherence. No unchanged full replay was run. Assembly parent: `1822c2ced32b123a02a938cbde9c80b26d639035`.
