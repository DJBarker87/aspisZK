# R363–R364 ControlFlow pattern diagnostic bundle

This package records a compiler-overlay build and one focused translation of the saved R334 ControlFlow source projection. It is diagnostic provenance only. R364 generated Lean was not compiled, and this bundle makes no theorem, source-to-model correspondence, compiler-correctness, cryptographic, or security claim.

## Contents and provenance

- `r362-api-inventory/` preserves the bounded API investigation, exact source excerpts, saved probe commands/output, snapshots, and its limitations. In particular, pinned Charon `NameMatcher.ml` and the same-image installed source bytes matched, but the object bytes linked into the earlier R349 binary were not established. The R349 `src/charon` link was dangling.
- `r363/` contains the two-file R363 source overlay, the R360 comparison, complete build and postbuild records, and all launch histories. `r363/preparation-history/` retains the earlier preparation README and review verbatim. The old R363 SHA inventory is retained there as historical; it includes the hash for the executable, whose bytes are intentionally excluded from this portable bundle. Its hash and retrieval are recorded in the successful build outcome and receipt.
- `r364-translation/` contains the exact LLBC input, launch and command records, binary binding, logs, generated `Types.lean`, `Funs.lean`, and `translation.json`. No executable or Lean cache is included.
- `r364-generated-source-census/` preserves the completed static census and checker. It is an inventory, not a semantic validation.

The R363 Aeneas source snapshot revision is `56a931fc3879354a2fa584e73bd0a1d412714851`; its local launch/campaign revision is `7c588ebcd62955448a0298b3d480aa7e23c408bb`. The separately saved R362 Charon source revision is `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`. These are kept distinct: the R363 source clone had no Git metadata, and the R362 inspection does not prove exact linked-object provenance.

## Build and translation records

The R363 cached release build exited 0 in 90.76 seconds. GNU time reports 589,484 KiB peak RSS; container cgroup sampling reports a 693,850,112-byte memory peak, zero swap, and no OOM event. Its output executable hash is `3dc9ad6de1af901c8ead41940ba97097a0cf06f82d27dbc7d7c5eac03695e329`; the 49,450,872-byte executable itself is not included. The saved postbuild audit found the two approved source differences from R360 (`NameMatcher.ml`, `llbc/LlbcAstUtils.ml`), all 313 changes since the R363 prebuild source inventory under `_build`, and zero shared regular-file inodes. Both earlier preflight failures are preserved; neither ran a build.

R364 translated the unchanged LLBC input (SHA-256 `8b9bd55e374866294b591758e1282d08998cb002e30b070207156b61f81a69ca`) with that R363 executable. The translation exited 0. It emitted three ControlFlow functions (`branch`, `from_output`, `from_residual`) and three ControlFlow inductives. The generated files are uncompiled. The translation result says `Lean_compiled: false` and `print_axioms: N/A; translation only`.

The completed R364 generated-source census is included byte-for-byte at `r364-generated-source-census/`. It reports no marker hits for `axiom`, `sorry`, `admit`, `opaque`, `unsafe`, `extern`, `implemented_by`, or external templates in the two generated Lean files; this static scan is not a proof or a semantics check.

## Limits and verification

No executable, `.olean`/`.ilean`, OCaml object/archive, build cache, or Python bytecode is included. The binary’s identity is retained by hash and receipt only. No translation was rerun while assembling this package, and no Lean compilation was run.

Run `python3 verify_evidence.py` from this directory to verify the file inventory and portable checksums. `inventory.json` maps each preserved file to its scratch provenance path and SHA-256; `SHA256SUMS` covers every regular file in this package except itself.
