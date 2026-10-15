# Route-guard focused Rust checks

This bundle records the focused feature-gated unit test and non-pool compile
check for the route guard in `programs/r1-cost-probe/src/lib.rs`.

The NUC source snapshot was copied from the split10 source workspace without
hardlinks. The baseline `lib.rs` hash was checked before overlay. The only
source path differing between the baseline and overlay manifests is
`programs/r1-cost-probe/src/lib.rs`. The source revision is
`3c79ec30fa44f408c716bb345050c137e907fa67`; overlaid `lib.rs` SHA-256 is
`36d36ee707f565df675db2ef7b2d27467f8b79bb99142c4b21d6fb7cc81910c9`.
`Cargo.lock` is pinned at
`f93f8f524fdd707c7a3b7feade31d015c891264b6c8fbd8bff885249e19600ea`.

The run used Cargo/rustc 1.94.1, offline locked release mode, two Cargo jobs,
and the existing v1.52 target cache. Each command had its own systemd scope
with `MemoryHigh=6G`, `MemoryMax=8G`, and `MemorySwapMax=0`.

| Check | Result | Wall time | Maximum process RSS | Swap |
|---|---:|---:|---:|---:|
| `pool_adapter_rejects_legacy_tags_before_borrowing_accounts` | passed (1 test) | 39.30 s | 483,920 KiB | 0 |
| non-pool `cargo check` | passed | 10.40 s | 510,396 KiB | 0 |

The exact commands and scope settings are preserved in `runner/run-tests.sh`;
outputs and `/usr/bin/time -v` receipts are in `results/`. Source manifests
record the copied baseline and the single-file overlay. This is focused local
compile/test evidence only; it makes no release-closure or protocol-security
claim.
