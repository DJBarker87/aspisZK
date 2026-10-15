# Candidate parser SBF build evidence

This bundle records the focused release SBF build with the isolated explicit-match field-parser candidate. The candidate source tree was copied from the prior P3 private-leaf-salts source tree; only `crates/aspis-core/src/field.rs` differs. `source-diff.txt` records the exact source hashes, and `source-manifest.sha256` pins every file in the 751-file candidate tree before the build. The same source candidate is preserved in the sibling `field-parser-candidate-20261014` evidence bundle.

The build used Solana `cargo-build-sbf` 2.3.0 / platform-tools v1.48 and the original `pool-adapter,private-leaf-salts` features, with `--locked -j 2`. It completed in 58.554 seconds under a 4 GiB high / 6 GiB maximum / zero-swap scope. The produced ELF and complete build log are retained. The log contains 57 lines beginning `Error:` in both the baseline and candidate runs; counts alone do not imply identical diagnostics. See `stack-diagnostics-comparison.json` and compare the full logs before drawing conclusions. No runtime transaction or cost gate was run.

`initial-launch-error.txt` records the first systemd invocation rejected before build start; the successful invocation omitted the incompatible `--wait` option while retaining the same resource caps.
