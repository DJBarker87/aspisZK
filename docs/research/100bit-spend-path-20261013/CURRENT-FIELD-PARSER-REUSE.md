# Current and historical field parser reuse

This is a source comparison, not a Rust-to-Lean refinement result. The three
current `field.rs` parser function bodies are byte-identical to the bodies at
the source revisions used by the historical R492 and R567 reports. That lets
the older work serve as a literal source reference for these routines, while
its Lean theorems still have a different parser interface.

## Source identity

The current worktree is at `8b62ca762b89b5af8f131d1c97a5c6d400df2a6b`.
Current `crates/aspis-core/src/field.rs` SHA-256 is
`3046536d04e84357c7df7bd742ec9839d1e1dc47ccc0ecaa59eb79ddec453c68`.
The whole file at both historical revisions below has SHA-256
`5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8`.

| Function | Current lines | Historical R492 lines | Current and historical body SHA-256 |
|---|---:|---:|---|
| `M31::from_le_bytes` | 239–245 | 175–181 | `61801dea89bcc6f411c3b373fcf966d9f257f4ca5b251f4b896c1c428c1102b7` |
| `CM31::from_le_bytes` | 410–414 | 346–350 | `b291b31b3aba3ab9ff3812e98f3d774577e69bba3cba57392d9bcb255d0a5f0b` |
| `QM31::from_le_bytes` | 1014–1018 | 934–938 | `3e58a8f03ca2ece6801dbfee02fa6b119fcde8c9f3240ab4f0c5e9e0e2b22a56` |

The historical commits are `d1d92d62a244732bc9ecf742e79fc05c7229ac5b`
(R492 report) and `6742daddf92657fee803c56f353415b9a882e8ff` (R567
report). At each revision, the parser bodies above have the same three hashes
as the current worktree. Run
[`tools/check-field-parser-reuse.py`](tools/check-field-parser-reuse.py)
from this repository to recheck the working-tree and both historical Git
objects. The script checks the named reference revision and source hashes,
reports the actual HEAD without requiring it to remain fixed, and performs no
build.

## Literal parsing behavior and old proof boundaries

Current `M31::from_le_bytes([u8; 4])` forms the little-endian `u32`, returns
`None` when it is at least `P = 0x7fff_ffff`, and otherwise returns
`M31(v)` (`field.rs:18–23, 238–245`). `CM31::from_le_bytes` parses the first
and second four-byte words as `a` and `b` (`:410–414`).
`QM31::from_le_bytes` parses `c0` from bytes 0–7 and `c1` from bytes 8–15
(`:1014–1018`), giving lane order `(c0.a, c0.b, c1.a, c1.b)`.

The R492 Lean model uses a different API. `R481NativeQM31Cell.decodeM31`
maps a 32-bit `BitVec` totally to a `U32`; `decodeQM31` extracts four
consecutive 32-bit lanes from a 128-bit cell (`R481NativeQM31Cell.lean:44–61`).
`R492ParserCellCanonical.lanes` fixes the same four-limb order and its
canonicality theorems require each lane to be `< P` (`R492ParserCellCanonical.lean:17–31, 44–73`). These theorems model total packed-cell decoding
and a separate canonicality test. They do not construct the cell from bytes
or model Rust `Option` propagation.

The V5 Lean byte model is closer to the current check. `decodeWordLE`
reassembles four mathematical bytes as a little-endian `u32`, and
`decodeM31LE` returns a value exactly when that word is `< P`
(`AspisFormal/V5ComponentCQM31Representation.lean:46–65, 90–115`). Its
QM31 decoder applies the same check to four limbs in the same order
(`:134–170`). The old interface
`ExactRustFriByteDecoderEquality` explicitly assumes equality between Rust
fixed-array decoders and these Lean functions
(`AspisFormal/V5MerkleConsumedValueBridge.lean:626–632`). The list and offset
theorems consume that premise; they do not prove it for the current Rust
functions (`:634–674`).

There is an input-width distinction. M31 takes `[u8; 4]`. CM31 and QM31 take
`&[u8]`, slice fixed ranges, and do not check the overall slice length: a too
short slice can panic before an `Option` is returned, while trailing bytes
after the consumed prefix are ignored. The Lean wrappers use `Fin 4` / `Fin
16` and `fixedBytes?`, which enforce exact width. Thus the parser bodies have
the same little-endian/range semantics when called on their exact-width
inputs, but the V5 equality premise still needs a width and byte-representation
bridge to establish the correspondence. In the current verifier, the QM31
callers pass 16-byte subslices; this note does not prove the call-site
relation.

The minimal reusable facts are the V5 `decodeM31LE` and `decodeQM31LE`
definitions, their canonicality checks, and
`exactRustFriByteDecoders_bind_all_fri_offsets`. The outstanding theorem is
the explicit equality premise for the fixed-width Rust decoders after mapping
the current byte arrays/slices into the V5 `Fin`-indexed byte model. Nothing
here connects the mixed 480/128-byte leaf assembly or the current verifier
flow to those per-value decoders.

## Existing extracted four-byte word identity

There is already a narrowly reusable Aeneas theorem for the arithmetic core of
the missing field-byte bridge. `AspisV8R19.SamplerWordBridge.four_bytes`
(`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/SamplerWordBridge.lean:26–32`)
states, without extra premises:

```lean
(core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).val =
  a.val + 256*b.val + 65536*c.val + 16777216*d.val
```

Its proof reduces `from_le_bytes` to `BitVec.fromLEBytes`, applies a symbolic
`byte_cons` lemma, and closes the polynomial rearrangement with `omega`. The
existing module imports `AspisV8R19.SamplerWordRead`,
`AspisV8R19.SqueezeOracleBridge`, and `AspisV8R19.SamplerWords`. The R76
receipt records this target as green (2.05 seconds, 3,706,620 KiB peak RSS,
zero swaps) in a two-target focused run that reused 328 cached targets. Its
audit lists `four_bytes` among the standard-axiom theorems; the old R76 opaque
formatter dependency belongs to `source_limb_exact`, not this lemma. Source
SHA-256: `f15b082b888ac9c0fddc08d00a6345a33f4cd6aa863fe5e43bd5a1f04930171f`.

The byte representation adapter is already explicit:
`SqueezeOracleBridge.encodeByte (b : DuplexFrames.Byte) : U8` is
`UScalar.ofNatCore b.val b.isLt`, and `decodeByte` returns the corresponding
`Fin 256` value (`SqueezeOracleBridge.lean:11–12`); `byte_roundtrip` and
`word_roundtrip` are at `:24–27`. The `Fin 256` domain agrees with the retained
codec's `Byte` alias (`RetainedFieldByteCodec.lean:20`), subject to the
namespace/type-alias conversion. The archived Aeneas `Scalar/Core.lean`
defines `U8.ofNat` as an abbreviation of `UScalar.ofNat` and proves
`U8.ofNatCore_val_eq` (`:687, 707–708`). That value theorem supplies the
per-byte equality needed after mapping `b : Fin 4 → Fin 256` pointwise through
`encodeByte`.

For an arbitrary four-byte input, the remaining proof plumbing is small and
explicit: show the `Array.make 4#usize` argument has the four mapped bytes in
the same order; use `four_bytes`; rewrite each mapped byte's `.val` to the
original `Fin 256` value; then identify the resulting weighted sum with
`RetainedFieldByteCodec.decodeWordLE b` (`RetainedFieldByteCodec.lean:31–40`).
The array/list indexing and the `U32.val` versus `Fin (2^32)` coercion need
their own stated equalities in that theorem. The current `four_contents` and
`source_word` lemmas (`SamplerWordBridge.lean:34–59`) establish the same fact
for four-byte slices extracted from a 32-byte sampler state, but are not
themselves arbitrary-input lemmas.

The R76 import cone is materially larger than the arithmetic theorem's proof:
its source file imports the three sampler modules listed above, and the
recorded focused compile had 328 cached targets. Its receipt explicitly says
`source_four_limb_value_assembly_matches_model: false` and
`complete_source_oracle_trace_correspondence: false`. Also, the historical
generated R66 field bundle contains no translated `M31::from_le_bytes`
function. Thus `four_bytes` can support the U32 value identity for an exact
four-byte input, but it does not by itself prove Rust's M31 range check,
`Option` behavior, CM31/QM31 slice assembly, or current call-site/source
correspondence. The earlier V5 decoder-equality premise remains necessary for
those parts until an explicit bridge is proved.
