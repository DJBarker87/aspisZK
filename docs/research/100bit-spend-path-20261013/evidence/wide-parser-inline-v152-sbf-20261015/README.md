# Wide parser inline experiment: v1.52 SBF build

This isolated experiment adds only `#[inline(always)]` immediately before `QM31::from_le_bytes` to the already translated two-QM31 half-parser candidate. The parser body and the `wide_exact.rs` candidate are otherwise unchanged. The 751-entry source manifest is retained under `source/source-manifest.sha256`; `results/source-manifest-prebuild.log` and `postbuild.log` record the exact source tree around compilation.

The build used the pinned Solana 3.1.13 / platform-tools v1.52 toolchain in a 4 GiB high / 6 GiB max / zero-swap / 128-task scope. See `results/inline-v152-sbf-build.json`, logs, and `toolchain-pins.txt`. It completed successfully. ELF SHA-256: `bbaf09e1c43d96cfcff88ea4e47e82bc4f67b9945d5f10861b45d10bf33fd4fe`.

`elf-comparison.json` compares the result with the preceding half-parser v1.52 ELF. `source/field-inline.patch` records the one-line source change relative to that candidate. No runtime source was changed by this experiment.

The generated task keypairs remain on the NUC. They are retained and were not deleted or copied into this evidence bundle.
