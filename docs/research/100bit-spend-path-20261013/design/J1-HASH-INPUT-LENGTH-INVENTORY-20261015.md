# J1 verifier hash-input length inventory

> Note (2026-10-19): the R1 proof format is now the compact binary-multiproof format, fixed length 57,607 bytes (`../evidence/format-adopt-20261019/REPORT.md`); 124,343 bytes below is the retired eight-way format.

This is a source-control-flow inventory at worktree revision `136b746805f3438507732622c9b4e50f36bf49f9`. It records byte counts visible at hash call sites for the `private-leaf-salts` S2 shape and identifies where checks occur before hashing. It does not establish a global bound for arbitrary callers of the verifier APIs or a Rust-to-Lean refinement.

## Source pins

| Source | SHA-256 |
|---|---|
| [`r1_wire.rs`](../../../../crates/aspis-r1-cost-probe/src/r1_wire.rs) | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| [`r1_semantic.rs`](../../../../crates/aspis-r1-cost-probe/src/r1_semantic.rs) | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| [`transcript.rs`](../../../../crates/aspis-r1-cost-probe/src/transcript.rs) | `c91ffe824a55ff62659e8a194d2ea201032383e4e11e5f60625404a30c691ef6` |
| [`verifier.rs`](../../../../crates/aspis-r1-cost-probe/src/verifier.rs) | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| [`transport.rs`](../../../../crates/aspis-r1-cost-probe/src/transport.rs) | `34af7f077fdae8147ebd79a44e7acb38395ec440115109c8fbfc654cb2c1e8c7` |
| [`lib.rs`](../../../../crates/aspis-r1-cost-probe/src/lib.rs) | `f68b59010023a1adc9aea104068bbfbd715a9e8d7daf1cc033e3e84406ba1402` |
| [`r1_pool_adapter.rs`](../../../../programs/r1-cost-probe/src/r1_pool_adapter.rs) | `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4` |
| [`state_only_private_merkle.rs`](../../../../crates/aspis-core/src/state_only_private_merkle.rs) | `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b` |
| [`r0/merkle.rs`](../../../../crates/aspis-core/src/r0/merkle.rs) | `6df6b25bf5b29dd2744af9db645e3c5818fa9256a454f175db4b750919ce7224` |
| [`pair_forest_semantic_terminal.rs`](../../../../crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs) | `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074` |
| [`pair_terminal.rs`](../../../../crates/aspis-statement/src/pool_v1/pair_terminal.rs) | `820710b2284ea967bb4b9a6d2ceb6cb171ac185b01df816db99db6ea78e629a3` |
| [`J1-SOURCE-CONFIGURATION-20261015.md`](J1-SOURCE-CONFIGURATION-20261015.md) | `f0e52b25e27c72b0202ff26641a3bfc02a4689b9b34d5b354ebd8ca4bd0bcf7d` |
| [`J1-SEMANTIC-PUBLIC-LAYOUT-20261015.md`](J1-SEMANTIC-PUBLIC-LAYOUT-20261015.md) | `d2b7e84f9993dca52722bbe883ef41e89affcfd3a0700378225d16ead8d2325a` |

The verifier crate labels this executable as an unproved cost probe. The pinned source-configuration inventory records research-branch split10 adapter/driver and arithmetic adoption, and no live deployment. The table below describes the inspected S2 `private-leaf-salts` branch; it is not a generic runtime proof.

## Pre-hash parsing and S2 framing sizes

The S2 proof-size formula is `View::proof_bytes` (`verifier.rs:37`), using `HEADER=16`, `SEMANTIC_BYTES=12903+29*32=13831`, `INITIAL_QUERY_BYTES=480+128+64+2*6*7*32=3360`, `SECOND_QUERY_BYTES=4*32+32+6*7*32=1504`, and `Variant::S2.final_len()=1024 >> 4=64` (`verifier.rs:8–18`, `transport.rs:5–9`). Thus a correctly shaped S2 proof is exactly:

`16 + 13831 + 29*32 + 32 + 7*32 + (32 + 7*32) + 64*32 + 22*(3360+1504) = 124343 bytes`.

`View::parse_shape` checks the header and variant, then requires `bytes.len() == proof_bytes(variant)` before slicing the proof (`verifier.rs:39–58`). `View::parse` then canonical-decodes the public challenge records and all query values, including the folded values for two-fold variants (`:61–76`). `tx1` calls `View::parse` before `r1_semantic::verify_observed` (`verifier.rs:342–349`), so malformed shape and canonical encodings are rejected before its first verifier hash. Strict `tx2` similarly calls `View::parse` before `resume` (`:360–365`). However, the pool adapter calls `tx2_authenticated` (`r1_pool_adapter.rs:970–977`), which calls only `View::parse_shape` before `resume` (`verifier.rs:380–385`): malformed length/header is rejected before its hashes, but this entrypoint does not rescan field canonicality before hashing. Its source comment requires an authentic tx1 checkpoint for the same immutable proof/public bytes (`verifier.rs:368–378`); that is a runtime precondition, not a local parser check.

Inside semantic parsing, `Prefix::parse` checks that the semantic bytes contain the C1 root, all 27 framed rows, and no trailing bytes (`r1_wire.rs:265–293`). `parse_record` enforces the row's exact tag and `5+payload` length, and for rows 14–26 canonical-decodes every WideExact payload word and rejects nonzero high components (`:38–74`). `SemanticTranscript::new` also converts the serializer-produced public-byte length to `u32` before its first hash (`:173–180`). These checks precede the corresponding hash operations. A proof that is structurally valid but fails a semantic boundary or terminal relation can, however, already have hashed earlier rows before rejection (`r1_semantic.rs:70–125`).

The semantic serializer emits 1455 bytes for transfer and 1427 bytes for withdrawal; see [`J1-SEMANTIC-PUBLIC-LAYOUT-20261015.md`](J1-SEMANTIC-PUBLIC-LAYOUT-20261015.md). With P3 semantic domain `UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3` (38 bytes), the first semantic-state hash input is `38 + 1 + 4 + public_bytes + 32`: 1530 bytes for transfer and 1502 for withdrawal (`r1_wire.rs:9–12,173–180`). The separate raw ASF8 terminal statement passed to the verifier adapter is 1880 bytes on the source route (`r1_pool_adapter.rs:965–968` and the statement codec); it is not the semantic serializer input.

For S2, row 25 carries `(87+29)*32=3712` payload bytes and a five-byte row frame (`r1_wire.rs:13–20,38–48`), so its semantic absorb hash is `32 state + 2 domain/row bytes + 3717 framed bytes = 3751`. Row 26 carries `29*32=928` payload bytes, hence a `967`-byte absorb input. Earlier semantic rows have no larger frame. The sample operation hashes the absorb, then a 33-byte squeeze, then a 33-byte advance (`r1_wire.rs:189–212`); the successful semantic prefix has rows 0–26, with row dispatch at `:342–365` and `r1_semantic.rs:77–130`.

## Hash-call families and input lengths

All lengths below are concatenated byte lengths under the supplied `HashFn`/`hashv` semantics.

| Call site | Input shape | S2 private-salt length |
|---|---|---:|
| Initial semantic state, `SemanticTranscript::new` (`r1_wire.rs:173–180`) | `DOMAIN(38) || [0](1) || public_len_le(4) || semantic_public || C1_root(32)` | 1530 transfer / 1502 withdrawal |
| Semantic row absorb (`r1_wire.rs:189–200`) | `state(32) || [0,0xa0+row](2) || framed_record(5+payload)` | row 25: 3751 maximum; row 26: 967 |
| Semantic row squeeze/advance (`r1_wire.rs:198–200`) | `state(32) || domain_byte(1)` | 33 each |
| Opening transcript initialization (`transcript.rs:7–12`) | `P3_DOMAIN(29) || variant(1) || semantic_state(32)` | 62 |
| Row 27 gamma absorb (`verifier.rs:87–90`, `transcript.rs:14–16`) | `state(32) || [DOM_ABSORB,row](2) || payload_len_le(4) || y1(29*32)` | 966 |
| Row 28 kappa absorb | same framing with 32-byte inactive scalar | 70 |
| Row 29 alpha0 absorb | same framing with seven E coefficients (`7*32`) | 262 |
| Row 30 alpha1 absorb (S2 only) | same framing with folded root(32) plus seven E coefficients(224) | 294 |
| Query row 31 absorb (`verifier.rs:97`, `transcript.rs:35–45`) | same framing with 64 E coefficients (`64*32`) | 2086 |
| Query row 31 expansion | eight `(squeeze,advance)` pairs, each hash input 33 bytes | 16 hashes × 33 |
| Row 32 rho absorb/block (`verifier.rs:98`, `transcript.rs:31–33`) | empty payload: `state(32)||row-frame(2)||length(4)`, then squeeze and advance | 38, then 33 each |
| C1 private leaf (`verifier.rs:247–250`, `state_only_private_merkle.rs:28–35`) | `[0x10,0x71](2) || packed480 || salt32` | 514 |
| C2 private leaf | `[0x10,0xf1](2) || packed128 || salt32` | 162 |
| Folded private leaf (`verifier.rs:254–262`) | `[0x10,0x72](2) || packed128 || salt32` | 162 |
| Merkle parent (`verifier.rs:120–128`, `r0/merkle.rs:20–31`) | `[0x18] || eight child digests (8*32)` as hashv slices | 257 |
| Checkpoint hashes (`verifier.rs:302–316,325–339`) | proof bytes; public bytes; then `"UNPROVED:R1:checkpoint"(22) || checkpoint_prefix` | proof 124343 on S2; adapter public 1880; checksum `22+(1768-32)=1758` |

For each successfully processed query, the verifier computes C1 and C2 leaf hashes, six radix-8 parents for each path, a folded leaf and six more parents: at most 21 hashes per query, or 462 across 22 queries. The control flow computes both C1/C2 leaf digests before testing either path, then checks C1 and C2 paths with short-circuiting; the folded leaf/path is reached only if both earlier paths pass (`verifier.rs:242–263`). Rejected canonical queries can stop after fewer leaf/parent hashes. All leaf and parent preimage widths remain the fixed values in the table.

The checkpoint has `checkpoint_size(S2)=1768` bytes (`verifier.rs:18,25`). On write, `checkpoint` hashes the proof, the passed `public` byte argument, and the checkpoint prefix (`:302–316`). On read, `resume` first checks checkpoint length/header/flags and then hashes proof/public and the checksum prefix (`:325–339`). The adapter supplies the exact 1880-byte encoded statement (`r1_pool_adapter.rs:890–893,965–975`). Stage 1 passes the parsed public account body into `tx1`; stage 2 re-encodes the validated statement, checks its exact 1880-byte length, then calls `tx2_authenticated`. The lower-level `tx1`, `tx2`, `tx2_authenticated`, and `resume` signatures themselves accept arbitrary `public_bytes: &[u8]`; absent the adapter's parser/length checks, the public-byte hash has no finite maximum from those function signatures alone.

## Maximum and scope boundaries

On the inspected pool-adapter S2 route, proof parsing fixes the proof length at 124343 bytes, public statement parsing fixes the raw public statement at 1880 bytes, and the private-leaf feature fixes every salt at 32 bytes. Among the enumerated verifier hash inputs, the largest for this route is the whole proof hash at 124343 bytes; this occurs while writing or reading the checkpoint. The longest transcript/Merkle inputs are much smaller: 3751 bytes for row 25 and 2086 bytes for the row-31 query absorb.

This maximum is conditional on that source route and S2 layout. It is not a global bound for direct calls with arbitrary `public_bytes`, and it is not a bound for every QV input in an abstract verifier model. The pre-hash rejection facts above distinguish strict parsing in tx1/strict tx2 from the authenticated tx2 path and concern inspected source control flow only. This inventory makes no exact global proof-length or deployment claim beyond those source expressions.
