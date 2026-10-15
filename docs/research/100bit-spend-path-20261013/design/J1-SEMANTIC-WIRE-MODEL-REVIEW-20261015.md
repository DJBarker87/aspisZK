# Review: `SemanticPublicWire` versus the §9 serializer

This is a mechanical layout comparison, not a Rust-to-Lean refinement or cryptographic conclusion. The current inspected source revision is `136b746805f3438507732622c9b4e50f36bf49f9`.

Pinned source hashes (SHA-256):

- [`pair_forest_semantic_terminal.rs`](../../../../crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs): `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074`
- [`SemanticPublicWire.lean`](../lean/SemanticPublicWire.lean): `f8a417abe539b13ca49bbcfa3cb3bb1ac40802acf2ce1ee22afc53a5173e4330`
- [`PublicOptionShape.lean`](../lean/PublicOptionShape.lean): `0fb33426084f3452a53dec73cf7c982e447a4c671e4bdf029807fbdc51232ae2`
- [`PublicFieldBlockCodec.lean`](../lean/PublicFieldBlockCodec.lean): `9b47ee332f677908c24cd2fa682c298fbcf207a91b5bec75aaa370c126137f65`
- [`PublicIndexListCodec.lean`](../lean/PublicIndexListCodec.lean): `122cda762fc4268fc30f20cbff666346c347e3c725294be997f602eeeebf5058`
- [`PublicByteCursor.lean`](../lean/PublicByteCursor.lean): `16466c8224a298122eedee57d02d8877e37769b9309dcfb7335a36aef433cff6`
- [`ExactLeafFieldCodec.lean`](../lean/ExactLeafFieldCodec.lean): `fd94743c7dde1d776dd2664d55d64be3774e6282ef1157ce35f1d7339e88a3e3`
- [`PublicIndexCodec.lean`](../lean/PublicIndexCodec.lean): `2ea8f5606b7b083b6032ee850709f825792726b29ff39ab0e8418e1a2b111645`
- [`R0P/Core.lean`](../../v8-r0-sem-proof-20261008/lean/R0P/Core.lean): `eba6bb784803b5f00922724efc9997a8d5ab6bc55cd8c100bffd8a397dabe1f9`

## Correspondence found

The Lean `encode` sequences at `SemanticPublicWire.lean:40–56` match the inspected `Public::public_bytes` order at `pair_forest_semantic_terminal.rs:1999–2040`:

- Both use variant tag `0` for private transfer and `1` for withdrawal.
- Both serialize anchor, nullifier, asset ID, optional-recipient flag/value, change, optional-amount flag/value, then the eight-byte next-pair index, snapshot frontier, next root, and next frontier.
- Transfer encoding places recipient flag `1` and recipient digest before change, then amount flag `0`. Withdrawal encoding places recipient flag `0`, then change, amount flag `1`, and the amount.
- The field codec is four-byte canonical little-endian M31; digests are eight M31 values (32 bytes), and frontiers are 20 digests (640 bytes). `PublicIndexCodec` splits the index into low then high 32-bit little-endian words, matching the byte order of Rust `u64::to_le_bytes` at the byte-layout level.
- `toPublic` at lines 32–38 maps those decoded fields into the `R0P.Public` field order. Its fields match `R0P.Public` at `R0P/Core.lean:56–67`.

The parser consumes the tag and then fixed-size fields using `PublicByteCursor.read` (`SemanticPublicWire.lean:62–65`; cursor implementation `PublicByteCursor.lean:11–13`). `decodeAfter` checks that its final remainder is empty (`:67–76`), so successful `parsePublic` rejects trailing bytes. Short fields fail through the fixed-width decoders. Unknown tags and wrong option flags also fail (`:58–60`, `:78–109`).

## Differences and boundaries to resolve or retain explicitly

1. **Withdrawal amount validation is in separate layers.** The Lean `parsePublic` applies `PublicOptionShape.check`, which rejects a withdrawal amount of zero (`PublicOptionShape.lean:19–26`). The Rust byte serializer itself only writes the `Option` flag and, for `Some`, runs the M31 field encoder (`pair_forest_semantic_terminal.rs:2026–2029`); it does not reject zero there. The terminal evaluation path rejects both zero and values `>= 2^30` in `composition_parts` (`:1234–1240`), reached by terminal composition (`:1303–1304`, macro wrapper `:1359–1368`). The wire parser's M31 decoder rejects noncanonical field values, but accepts canonical values in `[2^30, P)`; `parsePublic` itself only imposes nonzero, so it accepts some values the terminal validator later rejects. This is a parser-versus-terminal-validation boundary, not a byte-order discrepancy.

2. **Index range versus transition validity.** The Lean carrier uses `Fin (2^64)` (`SemanticPublicWire.lean:23`) and proves the mapped public index is below `2^64` (`:123–127`), matching the source `u64` wire width. It does not impose the pool capacity or transition checks. Rust `validate_transition` checks snapshot sequence/index equality, index capacity, increment by one, and frontier cells (`pair_forest_semantic_terminal.rs:180–208`), and `composition_parts` invokes it (`:1240`). `parsePublic` is therefore only a wire/option-shape decoder, not a full accepted-terminal validator.

3. **Intentionally absent data.** The wire model's `Common` omits pool, deployment domain, snapshot sequence, and current root; it carries only the values serialized by `public_bytes`. It also omits withdrawal destination token account. This matches the serializer body: its comment says pool/domain/sequence and source current root are not serialized (`pair_forest_semantic_terminal.rs:1999–2001`), and after the common public fields it writes only `source.next_pair_index`, `source.frontier`, `after.next_root`, and `after.next_frontier` (`:2030–2039`). The public mapping functions at `:1312–1345` populate pool/domain in the internal `SemanticPublic`, but that does not make them bytes in this layout.

4. **Envelope and broader inputs.** This parser does not model the ASF8 wrapper or account binding, as its module header states (`SemanticPublicWire.lean:6–9`). The separate full ASF8 statement is 1880 bytes (`pair_forest_terminal.rs:29–41,808`); it must not be conflated with the semantic `public_bytes` payload.

The layout offsets and lengths agree with the preceding [J1 semantic public layout inventory](J1-SEMANTIC-PUBLIC-LAYOUT-20261015.md). Remaining root question: should the Lean artifact be described strictly as a canonical wire-and-option-shape parser, leaving the source terminal's amount and transition validation explicitly downstream, or should a separate predicate model those downstream checks without changing `parsePublic`? No choice is made here.
