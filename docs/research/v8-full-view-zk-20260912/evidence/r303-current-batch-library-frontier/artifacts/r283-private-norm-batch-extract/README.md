# R283 private norm batch extraction preparation

This is a prepared, unlaunched extraction runner. The lead selected the single
root `crate::circle_norm::joined_inverse::line_norm::r110_norm::batch` after the
R280 diagnostic showed that its typed root graph does not reach the rejected
`Zip` trait implementation used by `try_norm`. R280 remains unchanged. This
selection does not change source, replace an operation, or weaken any proof
statement.

The command retains the frozen R266 source snapshot, source hashes, optimized
cached Charon/Cargo settings, `core::option` and `aspis_core::field` includes,
`--mir built`, and `monomorphize = false`. It writes only to the new R283 host
root and uses a dedicated user systemd unit/slice with `MemoryHigh=5G`,
`MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. The launch-preparation
revision is recorded as `380c7d46c9719dcfcab601fac2607861d47dee02`; the frozen
source tree has no Git metadata, so this is not represented as its revision.

`run_extract.py` performs remote preflight, configures the R283 slice, runs the
extraction, and copies outputs back. It has **not** been run here. The lead is
to launch only after R282 review. The expected diagnostic requirement is that
Charon's `has_errors` is false; any error output must be retained and reported,
not filtered or treated as proof evidence. This bundle contains no extraction
result and makes no source-semantics or proof-closure claim.
