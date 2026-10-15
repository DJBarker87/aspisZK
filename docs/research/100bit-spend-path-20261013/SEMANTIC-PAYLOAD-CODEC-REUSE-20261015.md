# Semantic payload codec reuse inventory (2026-10-15)

Source revision inspected: `6459d24bcd83bf12441b606d8031b6c9301bc320`.
This records source and formal interfaces only. Rust row facts below are not a
Lean correspondence theorem or a claim that the current S2 verifier parses
these records.

## Rust rows 0–24

`r1_wire::row_shape` gives the record tag and exact payload byte length. The
record is always `[tag][u32 little-endian payload length][payload]`
(`r1_wire.rs:38–48, 53–74, 76–86`). The duplex frame discriminator is a
separate byte pair `[0, 0xa0 + row]` (`r1_wire.rs:196–201`); it must not be
confused with the first byte of the framed record.

| Semantic row(s) | Record tag | Payload | Construction/use in current probe |
|---|---:|---|---|
| 0, 1, 3–13 | 0 | empty | Rows 0/1 are lambda/chi; rows 3–12 are ten `zc` challenges; row 13 is mu. `host_semantic.rs:84–91, 104–108`; `r1_wire.rs:341–365`. Although payload is empty, the framed message is the five bytes `[0,0,0,0,0]`. |
| 2 | 1 | 32 bytes | C2 Merkle root, absorbed to sample theta. The root is produced immediately before row 2 (`host_semantic.rs:102–103`). |
| 14 | 3 | 32 bytes | `WideExact::from_qm31(mask_sum).to_le_bytes()`, absorbed to sample eta (`host_semantic.rs:138–142`). |
| 15–24 | 2 | 28 consecutive 32-byte values (896 bytes) | Ten sumcheck messages. Each message serializes the 28 coefficients of the interpolated round polynomial as `WideExact::from_qm31` (`host_sumcheck.rs:44–74`; shape at `r1_wire.rs:44`). |

`parse_record` checks the exact total size, tag, and little-endian length;
for rows at least 14 it parses every 32-byte value as `WideExact` and rejects
nonzero high QM31 component (`r1_wire.rs:51–74`). `Prefix::parse` consumes the
C1 root and exactly 27 records (rows 0–26), rejects missing/trailing bytes, and
uses `parse_record` on every row (`r1_wire.rs:265–305`). `begin` samples rows
0, 1, 2, 3–12, 13, and 14 in that order (`r1_wire.rs:341–365`). The row 0
initial state hashes domain, a separator, checked `u32` public-byte length,
public bytes, then C1 root (`r1_wire.rs:163–180`). Each row hashes the previous
state, the row discriminator and framed record; squeeze and advance are from
the absorbed state (`r1_wire.rs:189–202`).

`host_semantic.rs:58–70` rejects C1 columns not of length 1024 and values
outside M31, and rejects noncanonical D/G QM31 byte encodings. It builds C1,
initializes the transcript with public bytes and C1 root, then emits the rows
above (`host_semantic.rs:72–103, 138–166`). For rows 15–24,
`host_sumcheck.rs:47–70` serializes each coefficient in array order. These
locations describe the current cost-probe path; `r1_wire.rs:1` labels that
module an unproved cost probe, so they do not establish production protocol
semantics.

## Existing Lean interfaces

The current generic duplex label model is
[`UnifiedLabels.lean`](lean/UnifiedLabels.lean:11): `label n` is the byte
`(160+n) % 256`; `label_val`, `label_injective`, and `row_label` establish
its arithmetic properties for `n < 33` (lines 14–32). Its file comment
explicitly does not identify this function with a protocol parameter's
`p.lbl` (lines 3–4). Thus the arithmetic byte is reusable, but the row-to-Rust
frame-label link is still a premise/adapter.

[`RawRoundDecode.lean`](lean/RawRoundDecode.lean:15) is a generic record
codec. `rawOf p j r` stores `p.lbl j` and `p.enc r.message`; `decode` checks
the label and runs abstract `p.dec`; `decode_encode`, `decode_length`, and
`decode_append_one` are generic facts (lines 18–38, 47–111). It does not
define the concrete Rust `record` framing or instantiate `M`, `p.enc`, and
`p.dec` with semantic payloads.

[`IndexedMessage.lean`](lean/IndexedMessage.lean:14) defines a one-message
read with three checks: indexed label equality, successful abstract decode,
and exact re-encoding equality. `read_encoded`, `read_sound`,
`read_bad_label`, and `read_noncanonical` are available at lines 22–53. This
is the appropriate generic place to enforce canonical encoded data once a
concrete semantic codec is supplied.

[`UnifiedSemanticRecovery.lean`](lean/UnifiedSemanticRecovery.lean:21)
defines `typed` as `InitialWalk.walk` followed by `RawRoundDecode.decode`.
`typed_before_row` (lines 26–45) proves recovery of the modeled prefix under
generic `p`, including explicit row-zero label/encoding hypotheses, a
consistent oracle trace, read budget and collision exclusion. It proves no
byte-level Rust parsing: the messages are values of arbitrary type `M`, with
abstract `p.enc`/`p.dec`.

[`UnifiedSemanticContext.lean`](lean/UnifiedSemanticContext.lean:16)
packages `{c1, records : List (Rec M), message : M}`. Its `parse` first applies
`parseAbsorb`, then `typed`, then `IndexedMessage.read` at `records.length`
(lines 21–25). `parse_sound` only decomposes success into those three
subresults (lines 36–62). It is a suitable generic context shell, not a
concrete byte parser.

[`UnifiedSemanticDecoder.lean`](lean/UnifiedSemanticDecoder.lean:20)
provides the completion tuple, `decode`, `decode_of_parse`, and `decode_sound`
(lines 20–80). It restricts to record lengths `0 < length < 26`; the decoder
output is a projection of the parsed generic context, not a decoded semantic
polynomial. [`UnifiedSemanticInjection.lean`](lean/UnifiedSemanticInjection.lean:21)
then connects this generic decoder to the modeled unified run for rows
`1 ≤ n < 26`, under its listed trace/read/label/row-zero premises. It does not
show the Rust byte parser produces its input context.

[`UnifiedRecords.lean`](lean/UnifiedRecords.lean:21) defines `previous`,
`absorbed`, and `records`; its messages are `payload : Nat → M`. The `records`
list is abstract and its next-state field is the unified modeled run state
(lines 21–43). `UnifiedSemanticRecords.records_eq` only identifies this list
with generic `RawRoundCompletion.recs` (lines 18–28).

[`UnifiedSemanticDensity.lean`](lean/UnifiedSemanticDensity.lean:26)
defines `DecodedSemantic` using old typed `SemMsgZ` values. Its
`semantic_density_bound` assumes a decoder function returning that type and
only supplies a density result when the returned semantic prefix length
matches the current prefix (lines 26–63, 69–88). The file header explicitly
leaves recovered-word, source-parser and acceptance implications open
(lines 6–8).

The older typed semantic model is in `R0P/MaskProtocol.lean:15–20`:
`SemMsgZ` is either `.base (SemMsg K)` or `.maskSum claim`, and `MsgZ` wraps it
in the typed semantic protocol. `R0P/MaskView.lean:14–32` maps those already
typed constructors to old views and extracts the row-14 `maskSum`; its
`semChalsZ`/`openingRoundsZ` functions parse lists of typed message/challenge
pairs, not byte strings (`:34–44`). `R0P/SemD2.lean` and `R0P/SemD3Glue.lean`
contain semantic bad-set and extraction lemmas over those typed values. A
search of the old v8 R0P semantic modules found no executable, strict
bytes-to-`SemMsgZ` or bytes-to-polynomial decoder.

## Available field parsers and missing connection

The Aeneas-derived [`CandidateFieldParsers.lean`](lean/CandidateFieldParsers.lean:78)
retains the Rust `M31::from_le_bytes` body and the nested CM31/QM31 parsers;
`parse_fields_probe` calls all three (lines 78–164). The equations preserve
`Option` failure for noncanonical M31 limbs. The adjacent
[`CandidateWideParserSource.lean`](lean/CandidateWideParserSource.lean:26)
contains the Rust `WideExact::from_le_bytes` parser and a probe wrapper
(lines 26–64); its header says this is an isolated candidate, not the deployed
runtime parser (lines 3–7). These are executable extracted parser bodies,
but this inventory found no theorem that composes them into the row-framing
parser or proves an exact typed semantic context.

The concrete adapters still needed to turn the existing generic interfaces
into a semantic payload codec are:

1. Decode and validate the five-byte record header against the expected row
   tag/size, then split its payload at exactly the Rust-defined boundaries.
2. Map row 2's 32 bytes to the C2 root; map row 14's 32 bytes to the
   `maskSum` constructor after strict `WideExact` parsing; map rows 15–24 to
   ten fixed lists of 28 strictly parsed `WideExact` coefficients, with the
   intended typed polynomial representation.
3. Give rows 0, 1, and 3–13 the exact message constructor/value whose concrete
   encoder equals the five-byte empty-payload record. Connect each source row
   to `p.lbl`, `p.enc`, and `p.dec`, and prove parser success implies
   canonical re-encoding.
4. Prove that the concrete row sequence and parsed message list coincide with
   the specific typed `SemMsgZ`/semantic-prefix context used by the old
   extraction lemmas. The current generic `M` context and typed old context
   are separate representations.

No source-correctness, probability, or security conclusion is made here.

## Source pins

| File | SHA-256 |
|---|---|
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/host_semantic.rs` | `113a367ae1e01d8fbd808ce3756b87040fd31ab359d94bad50b7c55c89c284bf` |
| `crates/aspis-r1-cost-probe/src/host_sumcheck.rs` | `f983229f9ea0c54954301c2dbb8255df6581a4def4f55d95b012c2bf47e9d1f1` |
| `lean/UnifiedLabels.lean` | `098500cbb77632628bb3c61d1c1e6ae35a64a73730424d9a75e91c5a73f42522` |
| `lean/RawRoundDecode.lean` | `19090c90c4856b85dd93497eb8dfa8e961992af8f27b14c631f5e805079d1dad` |
| `lean/IndexedMessage.lean` | `91a6a7defcfb799c8010c2667b8e8091149af323daa5cc81f03d2ef3c6b7ee26` |
| `lean/UnifiedSemanticRecovery.lean` | `971f84897f0c546fdd6488e197bc887062fb3904a4e520dc6595ada317a14d88` |
| `lean/UnifiedSemanticContext.lean` | `6df6dc438bb68d6d70dec97a756ced30934ee53a8b0731a0e43ccdbe07662fbd` |
| `lean/UnifiedSemanticDecoder.lean` | `146b09442030f22e7353c511c971376a0412a450d467c63c4997dd398b2b61ba` |
| `lean/UnifiedSemanticInjection.lean` | `ebf35f7daac011cb7725bd86f6076e59f719741b33c1ef0ae9b2a98c2cc2c1ec` |
| `lean/UnifiedRecords.lean` | `20ebb7340cb84a81f205cef47ea47849167f2bb61b750315a2d6614388a6d007` |
| `lean/UnifiedSemanticRecords.lean` | `85e696dc5ddfbb1524cc6599257513fd6674149eac6697446a6c29f96375e50b` |
| `lean/UnifiedSemanticDensity.lean` | `db2457d02da3ce58cec52092eab5cfbccdb4f820ed285a451c9dceb6223a0667` |
| `lean/SemanticPrefix.lean` | `a0e75d2bddea2f3d72b7102b29b099e3f552dd50114b255843685c75e8f23245` |
| `lean/CandidateFieldParsers.lean` | `8d5bd9a6ffda89e8c042bdd0202eb1b41ae6988296d3c6673a6f8fa9b07e4531` |
| `lean/CandidateWideParserSource.lean` | `5701830f4295c7da30152bc770132bd4dfda81e5682bbb05e49372c0dbcaaf3b` |
| `v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean` | `370faede24fa9a3afedb872da2d2e5843091d4653ad8a69f668d2facecc5aa5b` |
| `v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean` | `f27198834fa43256002cce83de7eeef675fecd88e89db0ee7a2bc00ef3a8b44b` |
| `v8-r0-sem-proof-20261008/lean/R0P/SemD2.lean` | `2b68437dfd6ba62cd023013a5b514987255550124c0eca4abb03a26a560397c0` |
| `v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean` | `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852` |
