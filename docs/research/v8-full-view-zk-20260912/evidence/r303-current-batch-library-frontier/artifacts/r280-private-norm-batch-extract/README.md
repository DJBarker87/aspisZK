# R280 private norm batch extraction (prepared only)

This directory prepares, but does not launch, one cached optimized Charon extraction from the pinned frozen source root. The selected roots are:

- `crate::circle_norm::joined_inverse::line_norm::r110_norm::batch`
- `crate::circle_norm::joined_inverse::line_norm::r110_norm::try_norm`
- `aspis_core::field::QM31::neg`
- `aspis_core::field::QM31::mul_m31`

The root list is disjoint from the previous R266 roots `B::neg` and `B::inv`; those existing private methods are reached from the new R110 functions and are not selected again as roots. `batch`'s saved R266 source body calls `.inv()`, and `try_norm` calls `.neg()`. The extra QM31 roots expose the exact source-field operations that the R156 field bundle does not provide.

The added field method spellings were verified read-only in frozen `crates/aspis-core/src/field.rs` (SHA-256 `639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499`): `QM31::neg` at line 874 and `QM31::mul_m31` at line 927. The prepared remote runner also verifies these method names, the `batch`/`try_norm` source names, all seven frozen source/manifest/lock hashes, and the exact Rust flags from saved R266 provenance before any extraction.

All extraction settings are inherited from R266: Charon preset `aeneas`, MIR `built`, default sysroot, `core::option` and `aspis_core::field` includes, `--offline --locked --release --jobs 1`, features `insecure-spend-fixture,selected-v7-kernels`, and the cached release workspace. The saved rustflags SHA-256 is `f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613`. The proposed output is `R280PrivateNormBatch.llbc` under the unique remote root `/home/dombarker/project-offloads/aspis-r280-private-norm-batch-extract-20261002-a`.

The launch-preparation Git revision is `e8601f2d13149484f3a6a0304cd48892821363c4`; the frozen source snapshot has no Git metadata, so exact source hashes remain the source identity. The runner retains the R266 resource envelope: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, in a dedicated systemd-run scope. Expected time is only cached optimized Charon extraction, not a full translation or proof. No extraction, build, translation, or theorem run has been launched from this directory.
