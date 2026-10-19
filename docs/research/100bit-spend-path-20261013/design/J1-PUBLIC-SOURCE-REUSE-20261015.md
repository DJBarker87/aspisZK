# J1 public serializer reuse inventory

Read-only source and artifact inventory at 3c79ec30fa44f408c716bb345050c137e907fa67. These are interface and provenance facts; they do not establish a Rust-to-Lean refinement.

## Current Rust entry and layout

The current method is r0::Public::public_bytes in [pair_forest_semantic_terminal.rs](../../../../crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs#L1989), SHA-256 2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074. The Public::semantic conversion dispatches to private_public / withdrawal_public (lines 1312–1345, 1990–1995). The serializer is lines 2002–2040.

The method builds a Vec<u8> in this order:

- variant byte 0 transfer / 1 withdrawal;
- anchor digest, nullifier digest, asset M31;
- recipient presence byte and optional digest;
- change digest;
- withdrawal-amount presence byte and optional M31;
- source next_pair_index.to_le_bytes() (8 bytes), source snapshot frontier, candidate next root, candidate next frontier.

Its local fields helper rejects any M31.0 >= P, then appends u32::to_le_bytes() (lines 2003–2011). The source asserts DIGEST_ELEMS == 8 (line 63), and the serialized snapshot frontier is [Digest; 20] (line 950). The method comment explicitly excludes pool, deployment domain, and the old/current root (1999–2001). The source types and conversions are concrete here, while the Lean wire type below is an independent mathematical carrier.

M31 is a public u32 newtype and P = 0x7fff_ffff in [field.rs](../../../../crates/aspis-core/src/field.rs#L19), SHA-256 28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea; its to_le_bytes is lines 248–249. The complete pair-forest semantic source hash above is the pin for the conversion and serializer together. History search for the exact pub fn public_bytes(self) declaration locates commit a383b9d5d74d904c028310981a24a656872885b0; no separate retained translation of this method was found.

## Existing Lean model and reusable theorems

[SemanticPublicWire.lean](../../../../docs/research/100bit-spend-path-20261013/lean/SemanticPublicWire.lean), SHA-256 cfc7a99fb041e9a7d2ad56d2fb5e02c1c18a4c8976c70e22af0672909a4b247a, defines Wire, Common, toPublic, and list-valued encode/decode. Its model layout (lines 18–56) has the same visible variant/option ordering and common fields. [SemanticPublicWireRoundTrip.lean](../../../../docs/research/100bit-spend-path-20261013/lean/SemanticPublicWireRoundTrip.lean), SHA-256 8b7e60052f40f7610ea3324c475cc766413c076e9a7505ed0278813332241d02, proves model-local decode_encode, encode_length (1455 transfer / 1427 withdrawal), and parsePublic_encode under PublicOptionShape.canonical (toPublic wire). SemanticPublicWireSound.encode_of_decode and SemanticPublicByteBinding.parsed_exact_bytes / bytes_unique concern successful parses of that Lean model. None mentions or takes the Rust Public::public_bytes function.

The relevant mathematical building blocks are PublicFieldBlockCodec.encodeFields / encodeDigest / encodeFrontier and their round trips (file SHA-256 9b47ee332f677908c24cd2fa682c298fbcf207a91b5bec75aaa370c126137f65), PublicIndexListCodec.encode / decode / length-8 round trips (SHA-256 122cda762fc4268fc30f20cbff666346c347e3c725294be997f602eeeebf5058), and PublicByteCursor.read_encoded / read_sound (SHA-256 16466c8224a298122eedee57d02d8877e37769b9309dcfb7335a36aef433cff6). They provide list-level codec facts, not source-body equivalence.

## Retained Aeneas material and extraction setup

No .lean file in the retained research tree declares or names Public::public_bytes; the retained generated files do include standard-library and field serialization models:

- [Vec.lean](../../../../docs/research/v8-full-view-zk-20260912/evidence/r319-current-batch-prefix-step-execution/library-source-preflight/Vec.lean), SHA-256 ebe737c37f7e0ca074b3de4edeaa2fba826952f7377d01317699e8e4e7b65f87, models Vec.new, Vec.push / Vec.push_spec, and Vec.extend_from_slice. The latter models cloning a slice and appending its list contents subject to the vector length bound (lines 352–363). This is reusable standard-library semantics; it is not a translation of the current serializer's call sites.
- [AspisR137Transcript/Funs.lean](../../../../docs/research/v8-full-view-zk-20260912/lean/AspisR137Transcript/Funs.lean), SHA-256 606f3dc4f140389e0a48fd173979f2fe6529dc151f7f839f04e81f5022969124, contains field.M31.to_le_bytes delegating to core.num.U32.to_le_bytes and CM31/QM31 slice-write functions (lines 36–117). The R318/R86 modules reuse Vec.push; they do not establish the public_bytes source relation.

The current [extract-field-parsers.py](../../../../docs/research/100bit-spend-path-20261013/tools/extract-field-parsers.py), SHA-256 3dccc0ea2c6ea0c4d5c40ef836aed287672bd64b59d8d87f1d8ab7d7c006841e, uses Charon at /home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon (binary SHA-256 b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c) and Aeneas at /home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/aeneas-repro-r1 (binary SHA-256 e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813), and supports a selected --entry/Charon --start-from extraction. Its retained field-parser attempts are under evidence/field-parser-extraction-20261014, evidence/field-parser-extraction-d-20261014, and evidence/field-parser-extraction-e-20261014. They target field parsers, not Public::public_bytes; no retained attempt translates this serializer, its local fields helper, or its Vec::extend_from_slice call chain. The existing extraction mechanism is therefore a possible tool template for a separately pinned isolate, not an existing result for J1.a.

A detailed earlier inventory, including the same source pins and the retained Vec/field APIs, is [J1-PUBLIC-SOURCE-EXTRACTION-REUSE-20261015.md](J1-PUBLIC-SOURCE-EXTRACTION-REUSE-20261015.md).

