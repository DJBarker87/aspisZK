# R575 verification receipt

## Exact result

- Canonical source: `AspisV8R19/R575NativeClaimHashCall.lean`, SHA-256 `848cc257012b4deb2f70ccd57809b924f3dbbeba40265c95b31c8c907c89717c`.
- Source revision recorded by the focused runner: `49388eacb2987708c48111ce0d9a35374a53f953`.
- Target: `AspisV8R19/R575NativeClaimHashCall.lean`.
- Lean: pinned 4.32.0 cache, `-j1 -M4500`; each attempt ran with MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128.
- Successful attempt: `1791083446250413000`, exit 0, wall 1.62 s, GNU-time Lean-child peak RSS 3,764,692 KiB, swap 0.
- Compiled olean SHA-256: `ecdde43059c2cfe9a60f0aa4cc12e688d9fa902cd85ff865662cac4d76064f16`; it is present in the pinned cache and saved with the evidence.
- Runner: `run_focus.py`, SHA-256 `d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea`.
- Direct input hashes are recorded in the attempt receipts. The final attempt imported R573 (`3c0b57b167b8e7808818bb876e4a6dc4d604f1691f7048aef4f6b16262f24d98`), R206 (`d2894672650838cb5baef289c06337917435438678ed295a98ec331f97287051`), and R152 (`72f534507c997ab67bf45efd08e459b76fc8dd43a3116467abc15d802e2cc3c7`). Exact dependency source copies are under `dependency-sources/`.

## Preserved attempts

| Run | Exit | Wall | Peak Lean-child RSS | Swap | Note |
|---|---:|---:|---:|---:|---|
| `1791083370470855000` | 1 | 1.71 s | 3,750,984 KiB | 0 | Earlier proof attempt; `sorryAx` remains in dependent declarations. |
| `1791083400214408000` | 1 | 1.75 s | 3,749,112 KiB | 0 | Follow-up proof attempt; `sorryAx` remains in dependent declarations. |
| `1791083446250413000` | 0 | 1.62 s | 3,764,692 KiB | 0 | Successful source snapshot; six complete axiom reports. |

Each exact `.source.lean`, `.log`, and `.receipt.json` is retained in its named attempt directory. The final source snapshot is byte-identical to the canonical source file.

## Complete axiom output for the successful target

- `claim_hash_address`: `[propext, Classical.choice, Quot.sound]`
- `begin_hash_execution`: `[propext, Classical.choice, Quot.sound, core.fmt.Formatter]`
- `checked_limit`: `[propext, Classical.choice, Quot.sound]`
- `absorb_map_short`: `[propext, Classical.choice, Quot.sound]`
- `claim_length`: `[propext, Classical.choice, Quot.sound]`
- `claim_absorb_execution`: `[propext, Classical.choice, Quot.sound]`

There are no `sorryAx` dependencies in the successful source snapshot. `core.fmt.Formatter` is the same opaque runtime type axiom identified in R569.

## Boundary

The theorem identifies the flattened hash argument for the claim-absorb call and preserves the arbitrary hash callback's result/error behavior in the expression. It does not prove a sampler execution trace or challenge distribution, a shared-oracle law, an adaptive-view simulator, probability losses, or end-to-end privacy/security.
