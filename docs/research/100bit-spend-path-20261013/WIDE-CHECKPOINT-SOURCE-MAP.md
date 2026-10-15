# Wide-field parsing and checkpoint source map

This source map records the pre-adoption baseline at Git revision `aba310f1daa065a27da89d15c6c47166037a8a71` (2026-10-15). The current research-branch adoption delta is recorded at the end of this document. It follows the R1 cost-probe verifier’s first transaction, strict second-transaction entrypoint, and checkpoint-authenticated second-transaction entrypoint. It records code paths and existing checks; it does not decide cryptographic sufficiency or establish a source refinement.

## Rust call flow

`crates/aspis-r1-cost-probe/src/verifier.rs:342-349` implements `tx1`. It calls `View::parse` (`:61-76`), then `r1_semantic::verify_observed` (`:345`), prepares the transcript/query state, checks the first `k` Merkle queries, and serializes a checkpoint. `View::parse` first calls `parse_shape` (`:38-59`) for the 16-byte header and exact proof length, then validates the typed proof regions:

- `echeck` (`:32-35`) visits exact 32-byte chunks and calls `WideExact::from_le_bytes`. With `k = true`, it also requires `x.c1() == QM31::ZERO`. `y1` is checked with this subfield condition (`:63`); `round0`, optional `round1`, and `final_message` are checked as canonical `WideExact` chunks (`:64-66`). The `inactive` value is decoded directly from its 32-byte slice (`:50`).
- Each of 22 initial query records is checked slot by slot for four slots (`:67-73`): 26 four-byte `M31` values in `q[s*120 + 4*l .. s*120 + 4*l + 4]`; a 16-byte `QM31` at `q[s*120 + 104 .. s*120 + 120]`; and two 16-byte `QM31` values at `q[480 + s*32 + 16*l .. +16]`. For two-fold variants, four 32-byte folded `WideExact` values are checked in the next 128 bytes (`:74`). Merkle siblings are fixed-width digest bytes, not field elements.
- The semantic prefix path is `r1_semantic::verify_observed` (`r1_semantic.rs:63-70`), which parses a `Prefix` and invokes `SemanticTranscript::new`/`begin` (`:72-78`). `Prefix::parse` reads the 32-byte C1 root, then framed rows 0–26 in order, rejects trailing bytes, and calls `parse_record` on each (`r1_wire.rs:265-293`). `parse_record` checks exact frame size, tag, and little-endian payload length (`:53-64`); for rows 14–26, every 32-byte payload value must decode as a canonical `WideExact` and have zero high `c1` component (`:65-72`). These rows include the ten 28-value polynomial rows, row-25 claims/mask payload, and row-26 `beforeZ1` payload (`:39-47`).
- Semantic arithmetic then reads checked low halves as `QM31`: `ValidatedRecord::decode_k` checks the requested range and decodes `part[..16]` after validating the 32-byte value (`r1_wire.rs:130-160`). The semantic verifier uses this for rows 14–26, the polynomial rounds, claims, extra values, and `beforeZ1` (`r1_semantic.rs:79-130`). The bytes validated by `parse_record` and the later low-half interpretation are separate Rust operations.

At the baseline revision recorded above, WideExact::from_le_bytes required
exactly 32 bytes, converted eight consecutive little-endian u32 limbs, then
delegated canonicality to from_limbs (wide_exact.rs:237-269; canonical
component limits were in :190-233). The baseline limb order was
(c0.c0.a, c0.c0.b, c0.c1.a, c0.c1.b, c1.c0.a, c1.c0.b, c1.c1.a, c1.c1.b)
(:237-248). The research branch now adopts h2: after an explicit 32-byte
length guard, it reads the same eight little-endian words with literal byte
indices and delegates to from_limbs; see the adoption metadata below. The
inline(always) annotation on from_le_bytes predates this parser change.
QM31::from_le_bytes and M31::from_le_bytes remain separate decoders in
crates/aspis-core/src/field.rs:239-249, 410-422, 1022-1025; QM31::from_le_bytes
has no inline(always) attribute in the current file or inspected historical
heads.

## Checkpoint and second-transaction paths

`checkpoint` (`verifier.rs:302-316`) serializes the fixed header and status, `hash(&[proof])` in bytes `16..48`, `hash(&[public])` in `48..80`, then transcript state, roots, challenges, query indices, semantic challenges, circle points, relation accumulators, and final weights. It appends `hash(&[b"UNPROVED:R1:checkpoint", &out])` over the preceding checkpoint bytes. The total length is `CHECKPOINT_FIXED + 16 * final_len` (`:18,25`).

`resume` (`:325-340`) checks checkpoint length, magic, variant, query count and reserved bytes (`:326`); checks both full-input digests and the domain-prefixed checksum (`:327-328`); then reads the stored fields. `Reader::e` decodes a checkpoint `WideExact` from exactly 32 bytes, and `Reader::k` decodes `QM31` from 16 bytes (`:318-323`). Checkpoint query indices must be below `2^18` and pairwise distinct (`:331-332`); the reader must end exactly before the trailing 32-byte checksum (`:336-339`). The checksum is an unkeyed hash; the entrypoint documentation explicitly requires the caller to supply a checkpoint produced by `tx1` for the same proof/public bytes and to protect the proof from writes (`:351-378`).

There are two second-transaction functions:

- `tx2` (`:360-366`) calls `View::parse`, repeating the full field scan, then `resume`, verifies remaining queries, and runs `finish_relation`.
- `tx2_authenticated` (`:380-386`) calls only `View::parse_shape`, then the same `resume`, remaining-query loop, and relation check. The active query call at `verifier.rs:265` is `crate::fast_dots::four_dots`, implemented in `crates/aspis-r1-cost-probe/src/fast_dots.rs:11-43` (SHA-256 `d57a0c97728ecec9cf768eceea8ae4578d18df976a8925abc6107d678e67ac9e`). It uses `unwrap()` on each query `M31`/`QM31` decode. A separate older `verifier::four_dots` helper remains at `verifier.rs:130-137`, but it is not the helper called by the current query path. The two-fold path reads its four 32-byte values through `weights::field` (`weights.rs:10`, called at `verifier.rs:269`). Relation checking also uses `weights::field` on round and final-message values (`verifier.rs:276-295`; `weights.rs:10`). These routines assume the exact slice widths and canonical inputs established by `View::parse`, or by the documented authenticated-checkpoint/proof immutability precondition in the second entrypoint; they do not independently return a parse error for those values.

The other field operations consuming those decoded values are `Prepared::new`'s seven-term claim combination (`verifier.rs:89-112`), active `fast_dots::four_dots` and circle/line folding (`fast_dots.rs:11-43`; verifier `:203-221`), query equality and accumulator update (`verifier.rs:265-274`), and round/pair/claim checks in `finish_relation` (`verifier.rs:276-297`). `weights::field` decodes one 32-byte `WideExact` at index `i` using `WideExact::from_le_bytes(...).unwrap()` (`weights.rs:10`); it does not itself decode seven coefficients. `verifier::polynomial` calls it for indices 0 through 6 (`verifier.rs:276`), while other consumers use their own loop bounds or selected indices: the two-fold query tail (`:269`), polynomial checks (`:282`), and final-message/weight pairing (`:293`). `weights.rs` has separate consumers with loop bounds determined by their inputs (`weights.rs:20-27,147-201`). These are the explicit current `WideExact` value-consumption sites in addition to parser and checkpoint decoding.

During each query, the verifier hashes C1 bytes `q[..480]` and C2 bytes `q[480..608]` into their tagged leaves (`verifier.rs:243-252`). With `private-leaf-salts`, these calls instead use those same payload ranges plus 32-byte salts at `q[608..640]` and `q[640..672]` (`:247-250`). In a two-fold variant it hashes the 128-byte folded leaf payload immediately after the initial query record (or payload plus a 32-byte salt for that feature) and authenticates its path to the stored folded root (`:253-262`). `merkle_path` hashes six 8-way parent nodes using the 224 sibling bytes per level (`:120-128`). This is separate from the three checkpoint hashes above.

The `resume` digest checks compare hashes of the complete current `proof` and `public` slices with the stored digests; they do not by themselves prove that the checkpoint was issued by `tx1`. `tx2_authenticated` retains that explicit caller precondition. This map makes no claim about collision resistance, checkpoint provenance, or whether a caller satisfies that precondition.

## Entrypoint and account provenance

The crate-level probe entrypoint is `process_r1_cost_probe_instruction` (`programs/r1-cost-probe/src/lib.rs:31-55`). For the direct `[1,k]`/`[2]` route, all three accounts must be owned by the verifier program and non-executable; only account index 2 (checkpoint) may be writable (`:36-38`). Stage 1 borrows proof and public data read-only, requires an all-zero checkpoint account (`:40-44`), calls `first`/`tx1` (`:24-27,42`), and writes the returned checkpoint bytes to account 2. Stage 2 calls strict `tx2` on the same readonly proof/public borrows and writable checkpoint borrow, then changes status byte 10 and recomputes the checkpoint checksum (`:45-47`). This direct local probe route does not derive a checkpoint PDA.

The pool adapter uses a different storage path. Its stage-1 handler (`r1_pool_adapter.rs:867-937`) requires a program-owned writable, nonsigner, non-executable proof account and a program-owned readonly public account (`:872-884`); it validates the ASPU header/body and zero checkpoint tail (`:899-928`), calls `first`/`tx1` (`:929`), and copies the returned checkpoint into the proof account tail (`:930-934`). Stage 2 (`:939-979`) validates the request and account set, immutably borrows the proof account (`:948-963`), and passes the proof body and appended checkpoint tail to `tx2_authenticated` (`:970-977`). `authenticate_asq8_accounts` requires proof, master, checkpoint, and lane accounts to be readonly and non-signers/non-executable with the expected owners (`:593-605`). It checks the checkpoint is owned by the pool program through that helper, binds its master and deployment domain, and verifies the checkpoint PDA from seed `aspis-pair-forest-checkpoint-v1`, master key, and little-endian checkpoint sequence (`:639-652`). This pool lifecycle checkpoint is distinct from the R1 checkpoint byte tail appended to the proof account.

The adapter’s lifecycle helpers also record authority and mutability rules: `lifecycle_accounts` requires an owned writable target and a distinct readonly signer authority (`:181-204`); initialization stores the authority in the account header (`:276-298`), writes are bounded by a kind-specific writable prefix (`:301-335`), and finalization validates the body before zeroing the authority bytes (`:338-359`). These are caller/account-flow facts from the prototype source, not a claim about deployment or cryptographic sufficiency.

Caller-source SHA-256 pins at this revision: `programs/r1-cost-probe/src/lib.rs` `66fcf176252443d0b3956797c8e854815cc8b6f8871a7cb5e246bea58dbf67fa`; `programs/r1-cost-probe/src/r1_pool_adapter.rs` `c47518022dd264be14172e2ac4d31c0fcf86725030ca6500afac9c549d5bb8fa`; `crates/aspis-r1-cost-probe/src/verifier.rs` `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd`; `crates/aspis-r1-cost-probe/src/weights.rs` `eb55a5a954f611828f03615a837a9298352a44a1c799a3e7726f8e1421c8d81a`.

## Existing checks and formal models

- `crates/aspis-core/src/field/wide_exact.rs` has unit tests `wide_exact_canonical_digits_and_bytes_roundtrip` and `wide_exact_rejects_malformed_encodings_without_panics` (`:532-602`). They cover 32-byte round trips, all eight limb positions, malformed lengths, and invalid representatives `P`, `P+1`, and `u32::MAX`.
- `crates/aspis-r1-cost-probe/tests/validated_prefix.rs` has `prefix_and_public_transcript_reject_bad_framing_and_field_encodings` and `semantic_rows_reject_noncanonical_limbs_at_every_wide_position` (`:32-105,108-168`). The latter checks every value/limb position in semantic rows 14–26, accepts low limbs at `P-1`, rejects `P`, `P+1`, and `u32::MAX`, and rejects a nonzero high-half limb.
- The exported `semantic_wire` module is a second, earlier S4 K-only wire/transcript copy (`lib.rs:5`; `semantic_wire.rs:38-72,95-105`), used by `semantic.rs`, not by `verifier.rs`'s `tx1` path. The current path imports `r1_semantic`, which uses `r1_wire`. Keep those similarly named parser implementations distinct when interpreting tests or source checks. Search of the current `aspis-r1-cost-probe` tests/source found no checkpoint-digest mutation or `resume` tamper test; the tests above exercise semantic wire framing/limbs, and the WideExact unit tests exercise its primitive decoder.
- `docs/research/100bit-spend-path-20261013/lean/RetainedFieldByteCodec.lean` defines little-endian four-byte words and canonical four-limb `QM31` decoding (`decodeWordLE`, `decodeM31LE`, `decodeQM31LE`, lines 23–136). `RetainedExactLimbCodec.lean` connects those four canonical residues to the exact `QM31` tower (`qm31ExactLimbEquiv`, lines 14–54). `ExactLeafFieldCodec.lean` gives strict 4-byte `M31` and 16-byte `QM31` list decoders with encode/decode round trips and successful-decode byte reconstruction. `MixedLeafEncoding.lean` and `MixedLeafDecoder.lean` prove the corresponding 480-byte C1 and 128-byte C2 leaf model identities; `LeafCodecCheckpoint.lean` audits these declarations. These are field/leaf byte-list model results; the later unrolled-wide checkpoint adds a separate extracted-model result for the wide parser. Neither result by itself proves compiler correctness or the complete View/checkpoint caller path.
- The evolving focused Lean evidence is recorded under [`lean-wide-parser-halves-20261015`](evidence/lean-wide-parser-halves-20261015/) and [`lean-strict-wide-codec-20261015`](evidence/lean-strict-wide-codec-20261015/). Those model the 32-byte/two-half representation and fixed-array slice operations; they do not identify the halves with the current Rust `WideExact` `c0`/`c1` fields or connect the model to `View::parse`/`resume`. The evidence directories preserve target receipts and source snapshots; this source map does not pin an in-progress target or infer Rust refinement from them.
- `M31ParserRefinement.lean`, `M31ParserCanonicality.lean`, `CandidateStrictQM31Parser.lean`, and `CandidateFieldCanonicality.lean` cover extracted/candidate M31 or QM31 parser bodies at fixed 4-, 8-, or 16-byte Aeneas array widths. `tools/check-field-parser-reuse.py` checks pinned `M31`, `CM31`, and `QM31` parser bodies. None of those declarations or checks covers the eight-limb `WideExact` decoder, row frames, `View::parse`, `resume`, or the unchecked stage-two call sites.
- `UnifiedDecoder.lean` and its component decoders dispatch over a generic Lean `Params`/oracle-table model; `UnifiedProtocol.lean` explicitly sets the framework decoder field to `none` and documents that the V3 statements proved there do not use that field. These modules do not encode the Rust proof/checkpoint byte parser. The newly isolated candidate parser is separately addressed by [`CandidateWideParserRefinement`](lean/CandidateWideParserRefinement.lean). The later root-adopted runtime parser uses the exact h2 unrolled candidate. The Lean theorem remains about the retained extracted model; it does not prove compiler correctness or link resume proof digest/checksum handling to successful field parsing.

The source comparison also searched the relevant historical heads `codex/r0-cost-probe-p1-20261009`, `codex/r1-precheck-p2-20261010`, `codex/z8-wide-batching-20261013`, and `codex/z8b-decomposition-20261013` for direct Lean declarations matching `WideExact.from_le_bytes` or a WideExact byte decoder; none was found. In their Rust source, the QM31 parser has no inline annotation and the WideExact parser is unannotated; its body uses fixed-array conversion, eight little-endian chunks, and `from_limbs`. This records the search result, not a claim about every historical branch or external library.

## Source pins

| File | SHA-256 |
|---|---|
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/semantic_wire.rs` | `58c671cee016246aa464a35ba443009813581e4a53bce37dd528d048009f2db7` |
| `crates/aspis-r1-cost-probe/src/semantic.rs` | `75d83ce86b203023c3a9a9d35420853b6a5a9196b634a971859f6f4b98b0d0c5` |
| `crates/aspis-r1-cost-probe/src/lib.rs` | `f68b59010023a1adc9aea104068bbfbd715a9e8d7daf1cc033e3e84406ba1402` |
| `programs/r1-cost-probe/src/lib.rs` | `66fcf176252443d0b3956797c8e854815cc8b6f8871a7cb5e246bea58dbf67fa` |
| `crates/aspis-r1-cost-probe/src/weights.rs` | `eb55a5a954f611828f03615a837a9298352a44a1c799a3e7726f8e1421c8d81a` |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs` | `c47518022dd264be14172e2ac4d31c0fcf86725030ca6500afac9c549d5bb8fa` |
| `crates/aspis-core/src/field/wide_exact.rs` (baseline at this map revision) | `56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea` |
| `crates/aspis-core/src/field.rs` | `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea` |
| `crates/aspis-r1-cost-probe/tests/validated_prefix.rs` | `e1d7c54e8981c724dcdf2490ccf55630fee72c8062eda466aa6951f43ea4e44b` |
| `docs/research/100bit-spend-path-20261013/lean/RetainedFieldByteCodec.lean` | `d29e2d982954b31fc3c68d225df3aa78124f153e9e2fcc99ffddca14f65fc18b` |
| `docs/research/100bit-spend-path-20261013/lean/RetainedExactLimbCodec.lean` | `c9988894652cc59e9b6ecb9a02e6fcf47164b503e365e1f8bee45f9d4d64b37f` |
| `docs/research/100bit-spend-path-20261013/lean/ExactLeafFieldCodec.lean` | `fd94743c7dde1d776dd2664d55d64be3774e6282ef1157ce35f1d7339e88a3e3` |
| `docs/research/100bit-spend-path-20261013/lean/MixedLeafEncoding.lean` | `775cd8c85f1920cefa73066a1fc7f56a34d1350bd3cb769b59f9132b9494a951` |
| `docs/research/100bit-spend-path-20261013/lean/MixedLeafDecoder.lean` | `f14e4bd4ec748f02163cfc125e069bb3b684d76982da41105d000b62ee9145a5` |
| `docs/research/100bit-spend-path-20261013/lean/M31ParserRefinement.lean` | `ba8e2b3be28c8bdfa2e4e7a35895c951225ec650aa9be3171d6b2f6e68c6d4d1` |
| `docs/research/100bit-spend-path-20261013/lean/M31ParserCanonicality.lean` | `59184c461c32151502268bc14c25502ae5e8f4e60ab44434320cbd7804b397d4` |
| `docs/research/100bit-spend-path-20261013/lean/CandidateStrictQM31Parser.lean` | `aeed259da29e525670c23e4a05341d563d3584c5a2f98bbd83c6b84fb57c390d` |
| `docs/research/100bit-spend-path-20261013/lean/CandidateFieldCanonicality.lean` | `2215d0356dac99ef0270dbe40c333a39c59527aff18eddf04f9fb6d63e24c23c` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedProtocol.lean` | `0087deb2a71b080806da8601bf469d623e06a4e83692cbf943339768f28ecb45` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedDecoder.lean` | `1627cc41fb098a7e9abe75184f0d00964b3374b46dd46e1c0ddd308a426b5090` |
| `docs/research/100bit-spend-path-20261013/tools/check-field-parser-reuse.py` | `1000e7fa60aa51fc9618106e2e4e4b9a26113ddc3d6e5013994d3bc30577b511` |



## Research-branch adoption delta

The root adopted the exact h2 unrolled wide parser on the research branch. Current crates/aspis-core/src/field/wide_exact.rs SHA-256 is 6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b; the prior baseline SHA in this map is 56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea. The adjacent field.rs remains byte-identical at SHA-256 28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea. Adoption details and package-entry validation are in [adoption.json](evidence/wide-parser-adoption-20261015/adoption.json).

The final [unrolled-wide checkpoint](evidence/lean-unrolled-wide-checkpoint-20261015/source-manifest.json) records 12 standard-only axiom reports for the retained-model bridge. This does not prove the Rust compiler/extractor translation or the whole verifier/security theorem. The source map above remains a record of its pinned baseline; historical checks and artifacts are not rewritten.
