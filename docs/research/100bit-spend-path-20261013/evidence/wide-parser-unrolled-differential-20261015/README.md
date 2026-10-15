# Unrolled WideExact parser and `from_limbs` differential

This host-only optimized Rust test compares the actual full baseline field module against the same full field module with candidate h2's `WideExact` implementation. The baseline uses `field.rs` SHA-256 `28df5a1a…f1baea` and `wide_exact.rs` SHA-256 `56c26ce3…068ea`; the candidate keeps the identical `field.rs` and uses h2 `wide_exact.rs` SHA-256 `6260fa9d…1d10b`. The candidate h source (`c8d01761…f9410`) was superseded before this test was launched and was not used in the run.

For every deterministic byte vector, the test observes both `from_le_bytes` implementations as `Panic`, `None`, or the returned eight limbs. For every exact 32-byte vector, it also decodes the eight little-endian `u32` words and calls both actual `from_limbs` implementations, comparing their outcomes with each other and with the corresponding parser outcomes. The 4,096 canonical-limb vectors must return exactly the original limbs. Coverage totals were 30,055 byte vectors, 60,110 parser calls, 13,607 `from_limbs` vectors, and 27,214 `from_limbs` calls.

The input family covers lengths 0–64, each possible byte at each of 32 positions, all eight limbs independently at `0`, `1`, `P-1`, `P`, `P+1`, and `u32::MAX`, pairwise boundary combinations, 256 deterministic random vectors per length, and 4,096 canonical eight-limb vectors. This finite differential result does not prove equivalence for all inputs or Rust source/compiler correctness, and it does not itself establish runtime adoption or an SBF cost result. A separate 13-pair h2 SBF cost measurement is recorded in [`wide-parser-unrolled-v152-cost-20261015`](../wide-parser-unrolled-v152-cost-20261015/README.md); it pins the same candidate source and ELF SHA-256 `ea9be844a7027f613cf310c5fedd54c8db9e6d669ba325af46d3b5908ef43796`.

The focused NUC command was:

```sh
ulimit -c 0
/usr/bin/time -v -o ../outer.time.log systemd-run --user --scope --quiet \
  -p MemoryHigh=4G -p MemoryMax=6G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/timeout 900 python3 run-differential.py --kit "$PWD"
```

The pinned compiler was `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM 22.1.6. Compilation passed in 4.93 s at 297,084 KiB peak RSS with zero swap. The one-test run passed in under 0.01 s at 2,816 KiB peak RSS with zero swap. The enclosing command took 4.99 s and peaked at 297,084 KiB. The cgroup limits were 4G high / 6G max / zero swap / 128 tasks. Full sources, runner, exact command outputs, timing logs, and hashes are retained below.
