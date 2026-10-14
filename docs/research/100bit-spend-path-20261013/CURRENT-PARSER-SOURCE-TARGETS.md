# Current parser, commitment-hash, and tx2 reload source targets

Read-only inventory pinned to worktree HEAD `d08448d3a0bcd78a777217eaa6594fc658115cc2`. The note was updated after locating the existing V5 per-field list decoders, exact-tower codec, and K1 successful-decode re-encoding lemmas. No builds were run. This note distinguishes the current cost-probe source from older Aeneas/Lean representation work; it does not assert a source refinement.

## Current Rust path

The current implementation is explicitly the R1 cost probe (`UNPROVED COST PROBE` file headers), under `crates/aspis-r1-cost-probe`.

| Operation | Current Rust declaration and behavior | Existing Lean/Aeneas target | Layout status |
|---|---|---|---|
| Semantic prefix/root framing | `r1_wire.rs:38-73` `row_shape`/`parse_record`: exact row tag, u32 LE payload length, and for rows ≥14 canonical `WideExact` plus zero high QM31 half. `Prefix::parse` at `:265-293` reads the initial 32-byte C1 root, rows 0–26, and rejects trailing bytes. `SemanticTranscript::new` at `:163-180` hashes domain, zero byte, u32-LE public length, public bytes, and C1 root. `r1_semantic.rs:70-77,155-163` parses this prefix, seeds the transcript with C1, and sets `roots=[c1_root,row2_payload]` (C2). | `PublicInitParse.parse` and `MerkleLeafCodec.parse` below are separate frame models. No Lean parser for this compact prefix or extraction of C1/C2 from its literal byte offsets was found. The V5 model does contain exact-width per-field `List Byte` decoders (one 4-byte M31 and one 16-byte QM31); those do not assemble or parse the current mixed 480-byte C1 and 128-byte C2 leaf layouts. | Rust current; no exact parser counterpart. |
| Strict C1/C2 leaf-value parse | `verifier.rs:36-78` `View::parse_shape` validates header, variant, exact proof length, slices query fields, and exposes `query`. `View::parse` at `:61-78` strictly scans all 22 queries: four 120-byte C1 slot groups, each 26 M31 words via `M31::from_le_bytes`, lane 28 QM31 at `slot*120+104`, and two C2 QM31 values at `480+slot*32+term*16`; two-fold query values are also scanned. Invalid encodings return `Error::Parse`. `fast_dots::four_dots` (`fast_dots.rs:11-40`) decodes the same offsets with unwraps after strict parsing. `verifier.rs:242-274` hashes leaves and verifies C1/C2 paths, with tags `0x71` and `0xf1`; the private-salt cfg passes a trailing 32-byte salt per leaf. | Current R1 `Merkle32Leaf.leafInput` and `MerkleLeafCodec.parse` are exact structural models of `0x10 || tag || packed || salt32` and tagged fixed-width frame roundtrip. They keep `packed` opaque: they do not parse 480 bytes as 4×(26 M31 + QM31), 128 bytes as 4×2 QM31, or prove `M31/QM31::from_le_bytes` correspondence. `CanonicalMerkleProgram`/`CanonicalMerkleRecovery` model arbitrary byte-list hash oracles and recovery, not this concrete field parser. | Structural leaf framing matches the private-leaf input format; internal C1/C2 decoder and Rust source behavior have no exact-current Lean counterpart. |
| Checkpoint write/hash | `verifier.rs:300-316` `checkpoint` writes `R1P2CKP2`, variant/next/status/reserved bytes, hashes of complete proof and public byte slices, transcript state, roots/challenges/queries/semantic values/circle points/claims/accumulator, then `hash(["UNPROVED:R1:checkpoint", prefix])`. | No current Lean serializer/parser for this checkpoint header, field order, hash domain, digest bytes, or accumulator serialization was found. `CanonicalByteHash` only encodes bytes to an abstract `Addr` and applies arbitrary `H`; it is not SHA-256. | No exact-current counterpart. |
| Checkpoint reload and strict tx2 | `Reader` and `resume` at `verifier.rs:318-340` check exact checkpoint size/magic/variant/status/reserved bytes/next≤22, proof hash, public hash, checksum, canonical field encodings, query ranges/distinctness, and final reader offset. `tx2` at `:351-365` first calls strict `View::parse`, then `resume`, processes remaining queries, and checks relation. `tx2_authenticated` at `:368-385` calls only `parse_shape` before the same `resume` and suffix; comments state its external checkpoint-provenance precondition. The simple entrypoint is wired at `programs/r1-cost-probe/src/lib.rs:36-48`; the Pool adapter writes tx1 checkpoint at `r1_pool_adapter.rs:905-934` and calls `tx2_authenticated` at `:954-974`. | Lean `UnifiedDecoder`/query models and generic `CanonicalByteHash` do not serialize or reload this checkpoint. The authenticated-parser audit is a source audit, not a Lean source-semantics theorem. | No exact-current counterpart. |

C1/C2 leaf hashing is `aspis_core::r0::merkle::leaf` (`crates/aspis-core/src/r0/merkle.rs:15-19`): `hash([0x10, tag], values)`. With `private-leaf-salts`, `state_only_private_merkle::private_leaf_hash` (`:22-35`) hashes `[0x10, tag] || value || salt32`. The Lean `leafInput` list grammar matches that byte shape for the salted case and for salt-free framing with an empty salt only if the caller uses a corresponding width convention; it has not been proved equal to these Rust `HashFn` calls. The generic Lean oracle abstracts hash semantics.

## Existing extracted / formal counterparts and their scope

- `docs/research/100bit-spend-path-20261013/lean/Merkle32Leaf.lean` (`leafInput`, fixed-tag leaf preimage lengths/injectivity) and `MerkleLeafCodec.lean` (`parse`, `parse_leafInput`, `parse_sound`) are current task Lean modules. They prove byte-list grammar facts. They do not model field element parsing, SHA-256, proof layout, or checkpoint reload.
- `CanonicalByteAddress.lean`, `CanonicalByteHash.lean`, `CanonicalMerkleProgram.lean`, and `CanonicalMerkleRecovery.lean` provide canonical byte-address normalization, an abstract oracle `H`, Merkle-program read traces, and generic recovery. Their exact theorem statements quantify over `H`; they do not bind `H` to the Rust SHA-256 function or to `tx1`/`tx2`.
- Older Aeneas-derived work under `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19` is reusable only as a raw representation/canonicality component. `R481NativeQM31Cell` proves four 32-bit lanes ↔ one 128-bit QM31 cell; `R492ParserCellCanonical` proves a scalar parser mask accepts exactly when the four limbs are `<P`; `QuarticInverseExecution` bridges canonical cells to an exact tower. The modules import `AspisR156FullFreeze`, are tied to prior source snapshots and do not implement current mixed 480/128-byte C1/C2 records or the current R1 `View::parse`/`resume`.
- `AspisFormal/V5ComponentCQM31Representation.lean` defines mathematical M31/QM31 finite codecs and `decodeQM31LE_encodeQM31LE`. `V5ComponentCQM31TowerExact.lean` transports `QM31Limbs` to the literal `QM31Exact` tower using `m31ResidueEquiv`, `limbsToQM31Exact`, `qm31ExactToLimbs`, and `qm31ExactLimbEquiv`; it also gives `decodeQM31ExactLE_encodeQM31ExactLE`. `V5MerkleConsumedValueBridge.lean:570-605` adds exact-length list wrappers `decodeM31Bytes` and `decodeQM31Bytes` (plus offset-based decoders); `exactRustFriByteDecoders_bind_list_decoders` at `:634-648` lifts a premise equating fixed-function Rust decoders to these wrappers. These APIs cover individual 4-byte/16-byte values, not mixed 480-byte C1/128-byte C2 assembly or current Rust parser semantics. `K1/V7Tag73SemanticTranscriptBridge.lean:438-505` proves the converse successful-decode identities `encodeWordLE_decodeWordLE`, `encodeQM31LE_of_decodeQM31LE`, and tagged exact-tower `encodeTagQM31ExactLE_of_decode` / `decodeTagQM31ExactLE_injective_on_success`. They are reusable byte-codec facts from the older Tag-73 layout, not R1 parser refinements. `V5InactiveClaimDeployedCorrespondence.lean:319-327` leaves `DeployedQM31CodecRoundTrip` as a named premise for another V5 wire layout; it is not a theorem for the current R1 parser.

## Source/refinement manifest observations

- `docs/research/100bit-spend-path-20261013/CURRENT-LEAF-CODEC-REUSE.md` is the current leaf inventory at base `496110fcb...`; its current source pins for `r1_wire.rs`, `r1_semantic.rs`, `verifier.rs`, `host_commitment.rs`, and `dense.rs` match the worktree hashes listed below. It reports the remaining mixed C1/C2 parser gap.
- `AUTHENTICATED-PARSER-AUDIT-SOURCES.json` says base `628054cd...`, `includes_uncommitted_p3_and_k11: true`, and pins source hashes for the parser/tx2 optimization. Its source files listed for this task still hash-match the current files below, but the manifest's historical base field is not a proof of current source refinement. `AUTHENTICATED-PARSER-AUDIT.md` explicitly labels the result a source audit, not a compiled source-semantics theorem.
- The older V8 `SOURCE_MANIFEST.json` pins target commit `9e432896...` (dated 2026-09-12). R481/R492/R567 reports carry their own historical source revisions (`b9ccc335...`, `d1d92d62...`, and `6742dadd...`, respectively). They must not be called exact-current parser extractions.

## SHA-256 pins

Worktree current Rust sources at `d08448d3...` (the relevant source hashes below remain unchanged):

- `crates/aspis-r1-cost-probe/src/r1_wire.rs` `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996`
- `crates/aspis-r1-cost-probe/src/r1_semantic.rs` `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3`
- `crates/aspis-r1-cost-probe/src/verifier.rs` `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd`
- `crates/aspis-r1-cost-probe/src/fast_dots.rs` `d57a0c97728ecec9cf768eceea8ae4578d18df976a8925abc6107d678e67ac9e`
- `crates/aspis-r1-cost-probe/src/host_commitment.rs` `551c4f8a0df50e0b53ab7e79d4e71b8c6afe417043c55caa1c377da3388f890c`
- `crates/aspis-r1-cost-probe/src/dense.rs` `572138d442d89643389595c515d3fbb7ee3d4e0868dd39228616ccebcb2dc6e2`
- `crates/aspis-core/src/field.rs` `3046536d04e84357c7df7bd742ec9839d1e1dc47ccc0ecaa59eb79ddec453c68`
- `crates/aspis-core/src/r0/merkle.rs` `6df6b25bf5b29dd2744af9db645e3c5818fa9256a454f175db4b750919ce7224`
- `crates/aspis-core/src/state_only_private_merkle.rs` `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b`
- `programs/r1-cost-probe/src/lib.rs` `66fcf176252443d0b3956797c8e854815cc8b6f8871a7cb5e246bea58dbf67fa`
- `programs/r1-cost-probe/src/r1_pool_adapter.rs` `c47518022dd264be14172e2ac4d31c0fcf86725030ca6500afac9c549d5bb8fa`

Current R1 task Lean sources:

- `lean/Merkle32Leaf.lean` `2d1f9ff2dc19bae994abbeda18ec96ae2654fecb1bc4873f2b3c4ae763f85ae8`
- `lean/MerkleLeafCodec.lean` `1f5614b0858ce2d77bffd3f706861b8bf4697960c83e11e12ef5e4d769eb9217`
- `lean/MerkleNodeCodec.lean` `db2499babc66c47c8a163e1c903f14a51421eb332721c15baec2c82b5c77eef4`
- `lean/CanonicalByteAddress.lean` `de19a4132c9e98b8c1a3b67a984c8055da34d672aa6fd9ff3ebe47ffd948967c`
- `lean/CanonicalByteHash.lean` `4521098a4b8b475c0b21cff79e2dce4bff86f7cd907e49f4b1630dd7a5230183`
- `lean/CanonicalMerkleProgram.lean` `52f1d15613025539d57cc415ed55919dc1cf190156fbda590f8c3a070a07efaf`
- `lean/CanonicalMerkleRecovery.lean` `5c5346a8b2dbe4b037adc63e37fad7a8ac360bbd63c68c15fbe518d86a9a5c79`

Older representation modules and manifests:

- `v8.../R481NativeQM31Cell.lean` `77fb6fd0d5e0e55c085541be65181f8ba3ca6905cd3daa33cef32c5e4c56efbd`
- `v8.../R492ParserCellCanonical.lean` `ab5066ac4caec99815aa578e45dff779059479ab870815c1aa63cb2d598d9eb8`
- `v8.../QuarticInverseExecution.lean` `8460530d030d61b07d980547934c3549a96680e6b8a175b5af5f65b1739f7168`
- `AspisFormal/V5ComponentCQM31Representation.lean` `a1be2908debd5f94bbb3570132a89818f582e061691b508557ad7e52691fb283`
- `AspisFormal/V5ComponentCQM31TowerExact.lean` `75404d16b5a71f67146b91ca35739b111f81bb730beb77432267f2b5385cebe5`
- `AspisFormal/V5MerkleConsumedValueBridge.lean` `8b5b329c813a208a81df8e219c901ac519ed48ef17192377004b9c526ac4c214`
- `AspisFormal/K1/V7Tag73SemanticTranscriptBridge.lean` `91ada7d79b858d045eacb57a4b8a34b5e01594800f8829fea0888b4820c3f189`
- `AspisFormal/K1/V7Tag73DeployedDecoderFiberCap.lean` `c6ccdaf7284edccbac0cce77088f547f33bc7568a2ddea8bd00041e315468c53`
- `AspisFormal/V5InactiveClaimDeployedCorrespondence.lean` `0caad4459de980eed222b41434fee201d609d81af152508ec1456fb78d82d8f8`
- `AUTHENTICATED-PARSER-AUDIT-SOURCES.json` `3ef22c04c74685c5d8d4c0bac2825f3d3e9bbe12898a407f5ad566fdd7da8960`
- `v8.../SOURCE_MANIFEST.json` `2b7dd5232a6bb86fa9df10ac382ce6f7d66cd3af6be54a68f5b70c89586f3413`
