# Current mixed C1/C2 leaf codec reuse inventory

## Current checkpoint update

The original inventory below records the earlier source review. The later
[leaf codec checkpoint](LEAF-CODEC-CHECKPOINT.md), based on
`d08448d3a0bcd78a777217eaa6594fc658115cc2`, reuses additional existing V5/K1
work: exact-length list decoders, successful-decode byte recovery, and the
literal field-tower equivalence. The new list wrappers and exact-field
wrappers are checked, as are lengths and injectivity for the mixed 480/128-byte
encoders. The remaining gap is an arbitrary mixed-leaf decoder and current
Rust correspondence, not the absence of all list-backed field codecs.

Relevant old APIs are `V5MerkleConsumedValueBridge.fixedBytes?`,
`decodeM31Bytes`, and `decodeQM31Bytes`; `V5ComponentCQM31TowerExact`'s literal
limb equivalence; and the two reverse codec theorems in
`K1.V7Tag73SemanticTranscriptBridge`. Direct imports exceed the configured
Lean threshold even in import-only probes. Source-pinned generators retain
those declarations in narrow modules; they do not modify the old files.
See the checkpoint for the one explicit Fin-index proof adaptation.

## Earlier inventory

Read-only inventory at source base `496110fcb2202fc8094191241f067a972071d396`. No source changes or builds were made. The dimensions below are the requested current R1 leaf layout, corroborated by the inspected host cost-probe writer and dense decoder: C1 has four slot-major groups of 26 M31 values plus one QM31 value (`4 * (26*4 + 16) = 480` bytes); C2 has four slot-major groups of two QM31 values (`4 * 2 * 16 = 128` bytes).

## Existing Lean APIs that can be reused

| Module / declaration | Exact useful type or premise | What it supplies / boundary |
|---|---|---|
| `AspisV8R19.R481NativeQM31Cell` (`lean/AspisV8R19/R481NativeQM31Cell.lean`) | `packWords (a b c d : BitVec 32) : BitVec 128`; `encodeM31 (x : field.M31) : BitVec 32`; `decodeM31 (x : BitVec 32) : field.M31`; `encodeQM31 (x : field.QM31) : BitVec 128`; `decodeQM31 (x : BitVec 128) : field.QM31`. Theorems `decodeM31_encodeM31`, `encodeM31_decodeM31`, `decodeQM31_encodeQM31`, `encodeQM31_decodeQM31`. | Exact reversible raw lane representation in order `c0.a,c0.b,c1.a,c1.b`. These are `BitVec` identities, not byte-list parsing or canonicality: `decodeM31` totalizes every 32-bit pattern to a U32-backed source M31. Source SHA `77fb6fd0d5e0e55c085541be65181f8ba3ca6905cd3daa33cef32c5e4c56efbd`; historical compile/revision metadata is in `R481_NATIVE_QM31_CELL.md`. |
| `AspisV8R19.R492ParserCellCanonical` (`lean/AspisV8R19/R492ParserCellCanonical.lean`) | `canonicalQM31 (x : field.QM31) := x.c0.a.val<P ∧ x.c0.b.val<P ∧ x.c1.a.val<P ∧ x.c1.b.val<P`; `decoded_cell_canonical_iff (x : BitVec 128) : canonicalQM31 (decodeQM31 x) ↔ canonicalPacked x`; `parserCellMask_accepts_iff (cells : List field.QM31) : scalar-mask-result=.ok 0 ↔ ∀x∈cells, canonicalQM31 x`; `packed_list_mask_exact (cells : List (BitVec 128)) : scalar-mask-result=.ok 0 ↔ ∀x∈cells, canonicalPacked x`. | Gives exact `< P` canonicality after raw 128-bit-cell decode and for the historical scalar mask. It assumes cells already represented as `field.QM31`/`BitVec 128`; it does not parse a `List Byte` into the four mixed C1 lanes. Source SHA `ab5066ac4caec99815aa578e45dff779059479ab870815c1aa63cb2d598d9eb8`. |
| `AspisV8R19.QuarticInverseExecution` (`lean/AspisV8R19/QuarticInverseExecution.lean`) | `decode (x : field.QM31) : QM31Exact`; `Canonical (x : field.QM31)` is the same four `< P` limb condition; `decode_encode (x : QM31Exact) : decode (encode x)=x`; `encode_decode (x : field.QM31) (hc : Canonical x) : encode (decode x)=x`. | Bridges generated U32-backed four-limb QM31 to exact `QM31Exact` under canonicality, and back. `QM31Exact := QuadraticAlgebra CM31Exact qm31R 0`, `CM31Exact := QuadraticAlgebra M31Exact (-1) 0`, `M31Exact := ZMod P`, `P=2147483647`, `qm31R=2+i`; see `AspisV8R15/ExactTowerBase.lean`. Does not consume bytes. Source SHA `8460530d030d61b07d980547934c3549a96680e6b8a175b5af5f65b1739f7168`. |
| `AspisV8R19.R144BeforeOodBytesBridge` (`lean/AspisV8R19/R144BeforeOodBytesBridge.lean`) | `cm31Bytes (q : AspisR137Transcript.field.CM31) : List U8`; `qm31Bytes (q : aspis_core.field.QM31) : List U8`; `qm31Bytes_length q : length=16`; `qm31_write_exact (q) (out : Slice U8) (hout : out.length=16) : write_le_bytes q out ⦃r => r.val=qm31Bytes q⦄`; `packed (xs : List aspis_core.field.QM31) := xs.flatMap qm31Bytes`; `bytes_exact`/`bytes_execution` prove the selected iterator serializer output. | Exact historical source writer bytes/order for a sequence of QM31 values (16 bytes each), not a mixed M31/QM31 C1 list parser. `qm31Bytes` uses `toR137QM31`; the current-to-before map direction is tracked by R196. Source SHA `e2d65628c0b3e8f3a836151bf3deec6f729f065be51197da9ed6845c4d605654`. |
| `AspisV8R19.R567ClaimSerializationInjectivity` (`lean/AspisV8R19/R567ClaimSerializationInjectivity.lean`) | `u32_to_le_bytes_injective`; `cm31_bytes_injective`; `current_qm31_bytes_injective (x y : field.QM31) (h : qm31Bytes (toBefore x)=qm31Bytes (toBefore y)) : x=y`. | Byte-list equality implies value equality for those selected serializers, including current QM31 after the explicit `toBefore` mapping. This is injectivity, not a list-byte parser or canonicality theorem. Source SHA `9c16521c7aa8e45b12debb467825244c102b429cb81f15aa30985b2a15e11dfd`. |
| `AspisV8R19.QuarticInverseExecution` source bridge APIs | `encode_canonical`, `decode_encode`, `encode_decode`; for canonical x, `encode (decode x)=x`. | A second, independent path to unique exact QM31 value from canonical generated limbs. It does not imply the `from_le_bytes` success relation for an arbitrary byte list. |

Historical report/source pins: `R481_NATIVE_QM31_CELL.md` records revision `b9ccc3356b15e1fbb459d7dfd4353dab96a3220a`; `R492_PARSER_CELL_CANONICAL.md` records `d1d92d62a244732bc9ecf742e79fc05c7229ac5b`; `R567_CLAIM_SERIALIZATION_INJECTIVITY.md` records `6742daddf92657fee803c56f353415b9a882e8ff`. These are separate generated-source snapshots; do not silently treat them as a compile of current Rust.

## Current Rust layout and parser references

The inspected current-worktree R1 implementation under `crates/aspis-r1-cost-probe` is explicitly marked **UNPROVED COST PROBE** in `r1_wire.rs`, `host_commitment.rs`, and related files. Its C1/C2 host writer is `host_commitment.rs:159-212`: C1 lane list is `0..25` followed by lane 28 (`:160-163`); C2 lanes are 26 and 27 (`:164`). Rows 0..25 are encoded from `M31` with 4-byte little-endian width, while lane 28 is encoded from QM31 and written at 16 bytes (`:184-202`). Slot is the outer loop (`:198`), giving 120 bytes per C1 slot and 480 total. The C2 writer uses the same slot-major loop and two 16-byte values per slot. `dense.rs:103-116` reads C1 from `q[..480]`, C2 from `q[480..608]`, decodes C1 M31s at `s*120+l*4`, lane 28 QM31 at `s*120+104`, and C2 at `480+s*32+(l-26)*16`.

The core field parser/writer is `crates/aspis-core/src/field.rs`: `M31::from_le_bytes([u8;4])` reads a little-endian u32 and returns `None` for `v >= P` (`:238-250`); `CM31::from_le_bytes` decodes two consecutive M31 limbs (`:410-419`); `QM31::from_le_bytes` decodes `c0` from bytes 0..8 and `c1` from 8..16, each via CM31 (`:1014-1023`). Thus one QM31 limb order is four 4-byte little-endian M31 values `c0.a,c0.b,c1.a,c1.b`. The Rust methods are length-sensitive by caller: `QM31::from_le_bytes` slices 0..16 and does not itself first check `bytes.len()==16`.

`r1_semantic.rs:25-38` has a different row-payload helper, `decode<const N>(row, bytes) -> Result<[QM31;N],Error>`: requires `N*32` bytes, rejects nonzero bytes `part[16..]`, then parses the lower 16 bytes with `QM31::from_le_bytes`. It parses 32-byte `WideExact` row values, not the mixed C1/C2 leaf. `r1_wire.rs:38-73` similarly frames semantic rows and for rows >=14 requires each canonical `WideExact` and zero high QM31 component; it does not type-decode the 480/128-byte commitment leaves. `host_semantic.rs:12-15` keeps C1/C2 behind an abstract `Commitments` trait and supplies 27 C1 columns / two C2 columns; it is not the concrete leaf parser. `dense.rs` contains the concrete byte offsets but uses unchecked `unwrap` in the cost-probe path.

The non-cost-probe `crates/aspis-core/src/circle_query.rs` is not the same shape: it uses 49 C1 M31 columns, C1 bytes `49*4*4`, and two helper QM31s; `proof.rs:96-97` declares the dimensions. `state_only_query.rs` uses selected 26-M31 C1 columns with two QM31 helpers but therefore has a 416-byte C1, and `state_only_spend_query.rs` adds a third QM31 helper to C2. Those are useful parser/kernel patterns but do not encode the current mixed 480-byte C1 slot (lane 28 QM31).

## Precise remaining representation gap

The reusable Lean proofs give (i) raw 128-bit QM31 lane reversibility, (ii) `<P` limb canonicality, (iii) exact-tower conversion under canonicality, and (iv) byte serializer injectivity for selected historical QM31/U32 encoders. They do **not** provide a theorem of the form `List Byte` of length 480/128 → current typed C1/C2 word, with success iff every M31/QM31 component is canonical and an encode/decode uniqueness law for the mixed slot-major order. In particular there is no direct bridge in these declarations from the current Rust `M31::from_le_bytes` / `QM31::from_le_bytes` success cases to `R481`'s `BitVec` decoder or to the exact tower. A source-level proof would still need the concrete byte slicing and LE-list/BitVec bridge, field-order mapping, parser failure relation, and the mixed 26+1 / 2 lane assembly.

This is an inventory only. It does not assert correspondence between the cost probe and production, and does not settle source security or any protocol gate.

## SHA-256 source pins

Current worktree sources at base above:

- `crates/aspis-r1-cost-probe/src/r1_wire.rs` `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996`
- `crates/aspis-r1-cost-probe/src/host_commitment.rs` `551c4f8a0df50e0b53ab7e79d4e71b8c6afe417043c55caa1c377da3388f890c`
- `crates/aspis-r1-cost-probe/src/host_semantic.rs` `113a367ae1e01d8fbd808ce3756b87040fd31ab359d94bad50b7c55c89c284bf`
- `crates/aspis-r1-cost-probe/src/r1_semantic.rs` `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3`
- `crates/aspis-r1-cost-probe/src/dense.rs` `572138d442d89643389595c515d3fbb7ee3d4e0868dd39228616ccebcb2dc6e2`
- `crates/aspis-core/src/field.rs` `3046536d04e84357c7df7bd742ec9839d1e1dc47ccc0ecaa59eb79ddec453c68`
- `crates/aspis-core/src/field/wide_exact.rs` `56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea`
- `crates/aspis-core/src/state_only_query.rs` `4e91b9b356998cc52f5482bc18c5de79b6dddeb9f9bb77bbf6af7d30ff401bd6`
- `crates/aspis-core/src/state_only_spend_query.rs` `03d959ba62591dfdd55173a45e55647f38d9a0f1aded7dae1f654913aca2f0ac`
- `crates/aspis-core/src/circle_query.rs` `5da1dbee29f3a052ad260ebbaeda0233dadb9ed3cf6d04f2a5c2cf84352e31de`
- `crates/aspis-core/src/circle_pcs_shape.rs` `0de69556b718b8184f6c65f698b6ce7e4347c80f652bd4e1a84fa7e7809e5093`
- `crates/aspis-core/src/proof.rs` `a8e3b259da25d47a3d88b38ca838d57ab104476929fe5758b43d1a37c06306a0`
- `crates/aspis-core/src/state_only_hiding.rs` `cc1039531cfe07518542d386668e9572e3eacf5127e8ec441c32bec20d116cd2`
