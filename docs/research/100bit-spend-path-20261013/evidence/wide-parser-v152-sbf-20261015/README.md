# Wide parser v1.52 SBF build

This evidence records one capped release SBF build for a source tree based on the earlier 751-file v1.52 field-parser candidate. The inherited `field.rs` is pinned to SHA-256 `28df5a1a…f1baea`. Relative to the earlier candidate, only `crates/aspis-core/src/field/wide_exact.rs` changed, from `56c26ce3…1068ea` to `940e31f8…d7d06`; the complete source manifest and exact byte diff are retained.

The build used Solana `cargo-build-sbf` 3.1.13 / platform-tools 1.52 and the existing v1.52 Cargo target cache. It completed with exit status 0 in about 22.0 seconds, sampled aggregate peak RSS 1,262,448,640 bytes, cgroup peak 995,016,704 bytes, and zero swap under a 4 GiB high / 6 GiB max / 0 swap / 128 task scope. Full command, resource receipt, and compiler output are in `results/`.

The output ELF is 1,217,920 bytes, SHA-256 `a12e57d6…c137be`. The mechanical comparison in `elf-comparison.json` compares it with the previous v1.52 candidate ELF (`fca47fb…6bea8`): section names/order/types match, while `.text`, `.data.rel.ro`, `.dynamic`, and `.rel.dyn` content hashes differ; `.text` is 1,544 bytes shorter and `.rel.dyn` is 176 bytes shorter. This is an ELF artifact comparison only. No runtime gate was run in this task.

The generated program keypair remains on the NUC at mode 0600 and is not included in this bundle; see `keypair-retention.txt`.
