# Merkle root parser and address inventory

Source inventory pinned to repository HEAD `3c8e4eb428875e27bf3a061acf2329b61a9d1a59` on 2026-10-14. This records source declarations and byte layouts only. It does not assert a Lean-to-Rust correspondence or make a security claim.

## Existing Lean encoders and parsers

`lean/PublicInitFrame.lean:12–45` defines the P3 initializer frame: the 38-byte ASCII domain `UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3`, a zero byte, four little-endian bytes encoding the public-byte length, the public bytes, then the 32-byte `State` value `c1`. `pre_length` and `frame_length` record the lengths; `addr_bytes` gives the full byte sequence for the resulting address. Here `State` is a 32-byte digest-shaped value.

`lean/PublicInitParse.lean:13–32` defines `parse`, which rejects public inputs whose length is at least `2^32` and delegates to `PrefixedStateCodec.parse`. `parse_addr` proves that `PublicInitFrame.addr` parses back to the supplied `c1`; `parse_sound` records the length guard and exact frame bytes. This parser is reusable as a C1 target predictor for this literal frame model. The source-level correspondence of this `c1` to the Rust C1 commitment, and its placement in the commitment-time trace, are not established by these declarations.

`lean/RowZeroCodec.lean` contains `row0_absorb`, identifying the empty row-zero record with `absorbA` at label 160. `PublicInitFrame.lean:49–61` defines the five-byte empty record and proves `row0_bytes` and `row0_prefix`; the latter shows its first 32 address bytes are the absorbed state bytes. These declarations concern the row-zero oracle address, not the C1 commitment-root field parser.

For Merkle leaf preimages, `lean/Merkle32Leaf.lean:14–20,65–87` defines `leafInput := 0x10 :: tag :: packed ++ salt` and the three specializations:

| Leaf | Tag | Packed bytes | Salt bytes | Total preimage bytes |
|---|---:|---:|---:|---:|
| C1 | `0x71` | 480 | 32 | 514 |
| C2 | `0xf1` | 128 | 32 | 162 |
| Folded | `0x72` | 128 | 32 | 162 |

`lean/MerkleLeafCodec.lean:11–16` parses a fixed tag and packed width, takes the trailing bytes as salt, checks the 32-byte salt width, and requires exact re-encoding. `parse_leafInput` (`:18–33`) proves encoder-to-parser roundtrip; `parse_sound` (`:35–50`) proves parsed values re-encode exactly. These parse leaf preimages, not the serialized fields carrying Merkle root digests.

`lean/Merkle32Path.lean` defines the 8-ary Merkle path and node input. `lean/MerkleNodeCodec.lean:12–17` reads eight 32-byte child digests following marker `0x18` and accepts only if `nodeInput children` exactly equals the input. `parse_nodeInput` (`:38–39`) and `parse_sound` (`:41–50`) are the encoder/parser roundtrip and soundness results for node preimages. `lean/MerkleChildTargets.lean` adapts this parser to a selected child slot; its stated scope is child targets.

`lean/MerkleProgram.lean:11–21,23–59` gives an oracle program for a supplied leaf and path. `eval_leafProgram`/`eval_pathProgram` express the trace and computed `foldPath`; `leafProgram_accepts_iff` and `pathProgram_accepts_iff` relate the returned digest to the supplied root. `lean/MerkleTable.lean:55–73` defines targets for a supplied root and node table. `lean/MerkleLeafRecovery.lean:45–64` defines recovery using supplied node/leaf tables and states a recovery-or-alternative result under a supplied root equality. These declarations do not parse C1/C2/folded serialized root fields.

## Rust commitment fields in the current wire source

The following are literal source layouts in `crates/aspis-r1-cost-probe` and are not proved equal to the Lean abstractions above.

- `src/r1_wire.rs:163–180`: `SemanticTranscript::new` seeds the transcript with the hash of `[DOMAIN, 0, u32_le(public_bytes.len()), public_bytes, c1_root]`.
- `src/r1_wire.rs:265–293`: `Prefix::parse` reads a 32-byte C1 root at byte offset 0, followed by P1 records 0 through 26 beginning at offset 32, and rejects trailing bytes. `row_shape` (`:38–48`) assigns row 2 a 32-byte payload. `src/r1_semantic.rs:70–77` passes the parsed C1 root to the transcript; `:155–163` sets verified roots to `[prefix.c1_root, prefix.payload(2)]`, taking the second root from row-2 payload.
- `src/prover.rs:207–238`: in the two-fold variant, the prover builds the folded tree, computes the round-0 message, then absorbs `folded_root || c1bytes` at transcript scalar row 30. In the serialized proof it writes semantic bytes, `y1`, inactive value, round-0 message, then the optional 32-byte folded root and 7-field-element `c1bytes`, followed by the final message.
- `src/verifier.rs:47–58`: `View::parse_shape` reads those fields in the same order and exposes `folded_root` as an optional 32-byte field. `:245–263` verifies query paths against the two prepared roots and, for two-fold variants, against the folded root using leaf tag `0x72` and path index `u/4`.

## Cases not represented by these parser declarations

The existing Lean declarations include the P3 initial-frame parser and its `parse_addr` roundtrip, as well as roundtrips for C1/C2/folded leaf preimages and Merkle node preimages. The inventory did not find a Lean byte parser/encoder roundtrip for the compact semantic-prefix C1-root field, the C2-root value sourced from semantic row 2, or the optional folded-root field in the proof suffix. It also did not find a theorem connecting the Rust root fields and their commitment-time placement to the corresponding Lean transcript values. These are source-inventory gaps only; this note makes no claim about their resolution elsewhere.

## Source hashes

SHA-256 of the cited source files at the pinned worktree state:

| Source | SHA-256 |
|---|---|
| `docs/research/100bit-spend-path-20261013/lean/PublicInitFrame.lean` | `756b529e3685c3341064b9970f5cebe71991b67eeeb5c6476a93934359f9a65e` |
| `docs/research/100bit-spend-path-20261013/lean/PublicInitParse.lean` | `cd7137ec47e4374dc3e776ab01638b12cc7a842920a38980f6fccdb9dbdf775a` |
| `docs/research/100bit-spend-path-20261013/lean/RowZeroCodec.lean` | `0ba6b54585a6fccc51f45a0993c596d1cf627d29c001c279ff8f5a1f00a344ea` |
| `docs/research/100bit-spend-path-20261013/lean/Merkle32Leaf.lean` | `2d1f9ff2dc19bae994abbeda18ec96ae2654fecb1bc4873f2b3c4ae763f85ae8` |
| `docs/research/100bit-spend-path-20261013/lean/MerkleLeafCodec.lean` | `1f5614b0858ce2d77bffd3f706861b8bf4697960c83e11e12ef5e4d769eb9217` |
| `docs/research/100bit-spend-path-20261013/lean/Merkle32Path.lean` | `93ef63727b5fc596eec0084ec737e921d54719e8a87d276cc151b3e8b2c28270` |
| `docs/research/100bit-spend-path-20261013/lean/MerkleNodeCodec.lean` | `db2499babc66c47c8a163e1c903f14a51421eb332721c15baec2c82b5c77eef4` |
| `docs/research/100bit-spend-path-20261013/lean/MerkleProgram.lean` | `cb3b6e45f30d41c9acac062d14e7f7bcba65ee41d60d4be4d65692804d2052e1` |
| `docs/research/100bit-spend-path-20261013/lean/MerkleTable.lean` | `3f474e66fced7516aef8732d2311f62be2228c34b697974172429198ad67a422` |
| `docs/research/100bit-spend-path-20261013/lean/MerkleChildTargets.lean` | `7ee0734898cac1b9ee689fea9111b02682bef5c22bbe44d8e82ba19c0069e904` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/prover.rs` | `a7e20e5eb2fb706f2bdb51371466d4ee02c6fcabc67a427495a3b9276d9495fd` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
