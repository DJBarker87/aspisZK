# R356 instantiated-name comment candidate — prepared, unbuilt

This scratch candidate applies only the lead-selected comment-formatting case to the R349 cached Aeneas source. In `extract/ExtractTypes.ml`, `extract_comment_with_span` now checks for `Types.PeInstantiated` names immediately after the `None` case and emits `Instantiated source name: [...]` using `name_to_string`. The previous two `Some` branches remain verbatim. The change avoids calling the pattern-name helper for that display-only comment case.

No shared helper, `extract_attributes`, Rust-model attribute, logical name matcher, source AST, LLBC, type/signature, source metadata, or other Aeneas source file was changed. The full parent and candidate `ExtractTypes.ml` files, unified patch, R349 baseline cache manifest, R356 candidate manifest, source snapshots for `TranslateCore.ml`, `InterpExpansion.ml`, and `PrePasses.ml`, and the recursive clone audit are saved here. The changed source file is `extract/ExtractTypes.ml` only; shared regular-file inode count between R349 and R356 source/cache trees is zero. The R349 cached executable is preserved unchanged in the clone.

The saved R349 tree manifest predates its successful native rebuild, so its `_build` artifacts differ from the current R349 tree. The clone audit uses that manifest to verify all non-`_build` source paths, then compares the complete current R349 and R356 trees directly. All cached build-tree records match; the only difference is the authorized `ExtractTypes.ml` edit.

This is preparation only. No build, translation, or Lean compilation was run. R223 owns the separate build runner/launcher; those files are outside this source audit and are not invoked here.
