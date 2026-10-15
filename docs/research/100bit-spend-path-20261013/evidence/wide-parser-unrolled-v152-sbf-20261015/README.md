# Unrolled wide parser candidate: v1.52 SBF build

This isolated candidate changes only `WideExact::from_limbs` and `WideExact::from_le_bytes` in `crates/aspis-core/src/field/wide_exact.rs`. The first uses eight explicit limb-range checks before the unchanged canonical construction. The second checks the input length and constructs eight little-endian `u32` limbs from literal four-byte arrays before calling the unchanged `from_limbs`. The function attributes and surrounding source remain as pinned. `source/wide-unrolled.patch` is the exact source patch; `source/source-manifest.sha256` pins 751 files and the pre/post-build verification logs report zero mismatches.

The SBF build used the pinned Solana 3.1.13 / platform-tools v1.52 toolchain, features `pool-adapter,private-leaf-salts`, and a 4 GiB high / 6 GiB max / zero-swap / 128-task scope. It completed in 22.02 seconds, with a 983,568,384-byte cgroup peak and no swap. ELF SHA-256: `ea9be844a7027f613cf310c5fedd54c8db9e6d669ba325af46d3b5908ef43796`.

`results/elf-comparison.json` compares section hashes with the field-only baseline and earlier half-parser variants. `results/cost-comparison.json` records the paired cost outcomes without making a semantic or security claim.

The first attempted build used a superseded source copy (`c8d01761…`) that had extra formatting changes. It was invalidated when the exact-source discrepancy was found; its source and partial logs are preserved in `attempts/superseded-c8/`. It produced no accepted ELF or cost result and is not used as evidence for this candidate.
