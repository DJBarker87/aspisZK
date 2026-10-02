# R296 pinned Charon option inspection

This is a read-only source inspection of the pinned Charon checkout at `/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon`, commit `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`. Exact source files were copied via SSH to `pinned-source/`; their hashes are in `source-hashes.json` and `checksums.sha256`. `relevant-source-excerpts.txt` preserves line-numbered portions used for the facts below.

`CliOpts.monomorphize` is a bool declared with `#[clap(long, visible_alias = "mono")]`, so source declares `--monomorphize` and alias `--mono`. Its doc says encountered items are monomorphized when possible, generic items are skipped, `--start-from` restricts to a particular call graph, and `dyn Trait` is unsupported. The distinct `monomorphize_mut` flag is optional-valued and uses `require_equals = true`; validation requires `remove_adt_clauses` when its value is `ExceptTypes`.

The `Preset::Aeneas` branch does not set `monomorphize` or `duplicate_defaulted_methods`; `CliOpts::validate` contains no monomorphize/preset conflict check. Thus the inspected source contains no rule rejecting `--monomorphize` with the Aeneas preset. No CLI parse or translation was run, so this is a statement about declarations and validation code only.

For defaulted methods, the copied translation source has a mono-mode early return in trait declaration translation with a TODO for default methods/default consts, and an early return for trait impl associated items. A separate non-early-return path reuses a trait default when an impl item has no explicit body. Duplication is a separate option/pass; Aeneas does not turn it on. Exact line excerpts and full byte-identical source copies are retained.

This inspection does not recommend or validate any semantic route for a future diagnostic and does not launch a build or translation.
