# J1 semantic public byte layout

This is a source-layout inventory of `Public::public_bytes`, not a source-refinement or security claim. The inspected worktree revision is `136b746805f3438507732622c9b4e50f36bf49f9`.

Source pins (SHA-256):

- [`pair_forest_semantic_terminal.rs`](../../../../crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs): `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074`
- [`pair_tree_profile.rs`](../../../../crates/aspis-statement/src/pool_v1/pair_tree_profile.rs): `8a7a4c7bdd3fe0ecd14d6fc920182be434ab92536924de22d269d906be3387b2`
- [`pair_terminal.rs`](../../../../crates/aspis-statement/src/pool_v1/pair_terminal.rs): `820710b2284ea967bb4b9a6d2ceb6cb171ac185b01df816db99db6ea78e629a3`
- [`payment_relation.rs`](../../../../crates/aspis-statement/src/pool_v1/payment_relation.rs): `8b543d3de5aa29d1e510e8ca18bd2bc6dae6c405b7d6f97402c572dfdbab2588`
- [`poseidon2.rs`](../../../../crates/aspis-statement/src/poseidon2.rs): digest width declaration `Digest = [M31; 8]` at lines 56–60 (hash not included here because only the layout files above were SHA-pinned in this inventory).

`Public::public_bytes` is at `pair_forest_semantic_terminal.rs:1999–2040`. Each M31 field is checked against `P` and emitted as four little-endian bytes (`:2003–2010`). Each digest is eight such M31 values, hence 32 bytes. The variant byte is transfer `0` or withdrawal `1` (`:2014–2017`). Optional-field flags are one byte from `Option::is_some()`.

## Transfer

The source mapping is `private_public` at `pair_forest_semantic_terminal.rs:1312–1327`; `Public::semantic` dispatches to it at `:1989–1995`. Offsets below are zero-based half-open ranges; the one-byte flags are shown as their byte offsets.

| Offset(s) | Width | Serialized field | Value/source |
|---:|---:|---|---|
| 0 | 1 | variant | `0` (`PrivateTransfer`) |
| 1–33 | 32 | anchor | `public.anchor_root`, 8 M31 |
| 33–65 | 32 | nullifier | `public.nullifier`, 8 M31 |
| 65–69 | 4 | asset_id | one M31 |
| 69 | 1 | recipient-present flag | `1` |
| 70–102 | 32 | recipient | `public.recipient_commitment`, 8 M31 |
| 102–134 | 32 | change | `public.change_commitment`, 8 M31 |
| 134 | 1 | withdrawal-amount-present flag | `0` |
| 135–143 | 8 | source `next_pair_index` | little-endian `u64` |
| 143–783 | 640 | source `frontier` | 20 digests × 32 bytes |
| 783–815 | 32 | afterstate `next_root` | 8 M31 |
| 815–1455 | 640 | afterstate `next_frontier` | 20 digests × 32 bytes |

Total: **1455 bytes**. This independently matches the expected transfer length. The `source` fields are from `PoolV1PairLiveSnapshotV1` (`pair_tree_profile.rs:397–404`); the afterstate fields are from `PoolV1PairVerifiedAfterstateV1` (`pair_terminal.rs:116–120`). The serializer includes `source.next_pair_index` and `source.frontier`, but not `source.sequence` or `source.current_root`.

## Withdrawal

The source mapping is `withdrawal_public` at `pair_forest_semantic_terminal.rs:1330–1345`; `Public::semantic` dispatches to it at `:1989–1995`.

| Offset(s) | Width | Serialized field | Value/source |
|---:|---:|---|---|
| 0 | 1 | variant | `1` (`Withdrawal`) |
| 1–33 | 32 | anchor | `public.anchor_root`, 8 M31 |
| 33–65 | 32 | nullifier | `public.nullifier`, 8 M31 |
| 65–69 | 4 | asset_id | one M31 |
| 69 | 1 | recipient-present flag | `0` |
| 70–102 | 32 | change | `public.change_commitment`, 8 M31 |
| 102 | 1 | withdrawal-amount-present flag | `1` |
| 103–107 | 4 | withdrawal amount | `M31(public.amount)` |
| 107–115 | 8 | source `next_pair_index` | little-endian `u64` |
| 115–755 | 640 | source `frontier` | 20 digests × 32 bytes |
| 755–787 | 32 | afterstate `next_root` | 8 M31 |
| 787–1427 | 640 | afterstate `next_frontier` | 20 digests × 32 bytes |

Total: **1427 bytes**. This independently matches the expected withdrawal length. The withdrawal source struct also has `destination_token_account` (`payment_relation.rs:58–68`), but `withdrawal_public` does not copy it into `SemanticPublic`, and `public_bytes` does not serialize it. Similarly, `pool` and `deployment_domain` are present in `SemanticPublic` (`pair_forest_semantic_terminal.rs:87–98`) and populated by both mapping functions, but are not appended by `public_bytes`.

## Distinction from ASF8

These 1455-byte and 1427-byte lengths are the semantic transcript bytes returned by this `Public::public_bytes` method. They are distinct from the full **1880-byte ASF8** terminal statement: `pair_forest_terminal.rs:29–41` identifies the ASF8 framing and its size expression, and line 808 asserts the 1880-byte constant. The ASF8 input is a separate encoded statement format; it should not be used as the length of `Public::public_bytes`.
