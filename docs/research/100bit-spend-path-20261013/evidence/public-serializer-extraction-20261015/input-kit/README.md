# Public serializer source-fragment kit

This kit prepares exact source spans for review before any Aeneas/Charon run. It extracts 19 declarations required to keep the current `r0::Public::public_bytes` method in its original source context: the `r0::Public` enum and its `semantic`/`public_bytes` methods, `CompiledVariant`, `SemanticPublic`, both conversion functions, the transfer/withdrawal public structs, live snapshot, late public statement, verified afterstate, `Digest`, `M31`, `P`, the pair/tree depth constants, and the R0 error enum.

`extract.py` copies bytes from the checked-out source files without rewriting declaration bodies. `source-manifest.json` records each original repository path, full-file SHA-256, UTF-8 byte span, exclusive line span, anchor, and exact copied-fragment SHA-256. It also records the generated `lib.rs` hash and each inserted-fragment output byte span. `source-pins.json` uses the `{"sources": {path: {"sha256": ...}}}` input format expected by the existing field-parser extraction runner, covering `Cargo.toml`, `lib.rs`, the layout template, and fragment files. Fragments live under `fragments/` as separate files. `layout.template.rs` supplies nested module namespaces/import bindings. The generator renders it to `lib.rs` by inserting every fragment as its original byte sequence (no `include!` appears inside an `impl`), including at the original `r0::Public` path and feature gate; it does not rewrite declaration bodies or substitute reachable dependencies. `Cargo.toml` names this extraction-input crate, but no build has been run.

Run from any directory:

```sh
python3 docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py
python3 docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py --check
```

The checker compares current source spans and full-source pins with every stored fragment, rendered `lib.rs`, source-pins manifest, and source manifest. It retains the originally recorded source revision and verifies each source hash/span directly; unchanged relevant files therefore do not fail solely because HEAD moved. It is a source-copy integrity check only; it does not compile Rust, run Charon/Aeneas, or establish serializer semantics.

The layout is an extraction-input scaffold and has not been claimed or checked as a complete standalone Rust dependency closure. `public_bytes` is inside `pair_forest_semantic_terminal::r0::Public`; it calls `self.semantic()`, and the resulting types include crate-owned field and statement types. If the extraction tool reports additional reachable functions/types, preserve their original declarations and module paths and record the dependency before proposing any isolate. Do not replace the serializer, its local `fields` helper, or reachable conversion code with a shim.

The source revision is recorded in the manifest. Current primary source pins are also visible there. In particular, the serializer and its wrapper/conversions come from `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`; the public payload types come from `payment_relation.rs`, `pair_tree_profile.rs`, and `pair_terminal.rs`; field representation and error type come from `aspis-core` sources.

## Prepared extraction runner (not executed)

`run-public-serializer-extraction.py` adapts the retained field-parser runner for this crate. It pins the same Charon/Aeneas binaries, verifies `source-pins.json` and fragment hashes, uses a fresh output directory, and explicitly invokes Cargo with `--no-default-features --features r0` so the target is not compiled out. The minimal package has its own `[workspace]` root and no external dependencies. The default Charon start item is `crate::pool_v1::pair_forest_semantic_terminal::r0::Public::public_bytes`; this method-path syntax remains to be confirmed by root before launch.

The exact proposed capped NUC command is:

```sh
systemd-run --scope --unit=aspis-public-serializer-extract-a \
  -p MemoryHigh=4G -p MemoryMax=6G -p MemorySwapMax=0 -p TasksMax=128 -- \
  /usr/bin/timeout 900 python3 /home/dombarker/project-offloads/aspis-r1-public-serializer-input-20261015/run-public-serializer-extraction.py \
  --input /home/dombarker/project-offloads/aspis-r1-public-serializer-input-20261015 \
  --output /home/dombarker/project-offloads/aspis-r1-public-serializer-20261015-a
```

No run has been started. Expected work is the isolated package's release compilation and lock generation, then Charon MIR extraction and Aeneas translation. Confirm host reservations and the entry name before launch; do not reuse an output directory.
