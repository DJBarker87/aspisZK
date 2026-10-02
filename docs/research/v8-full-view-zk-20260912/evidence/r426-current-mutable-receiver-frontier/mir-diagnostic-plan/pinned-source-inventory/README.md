# Pinned Charon MIR-output inventory (read only)

## Finding

Pinned Charon has no CLI option or existing logging switch that prints the selected nonlocal rustc MIR body before operand translation. Its print switches emit Charon ULLBC/LLBC. The existing R426 run already used `--print-original-ullbc`; in that earliest Charon representation, `Iterator::try_fold` contains `_5 = TraitClause0::next<'4>(copy self)`. That establishes the copy is present by the earliest saved ULLBC stage, but ULLBC has already translated from Rustc MIR and does not preserve rustc's `WithRetag` annotation. It cannot tell whether MIR had `Copy`, `CopyForDeref`, `Rvalue::Ref(&*self)`, or another form.

The source-defined option boundary is:

- `options.rs:256–271` has `--print-original-ullbc`, `--print-ullbc`, `--print-built-llbc`, and `--print-llbc`. The documented stages are ULLBC after MIR extraction, post-micro-pass ULLBC, reconstructed LLBC, and final LLBC.
- `transform/mod.rs:85–89` runs the `print_original_ullbc` pass immediately after translation from MIR. It receives Charon's translated context, not the raw `rustc_middle::mir::Body`.
- `get_mir.rs:89–106` chooses `tcx.optimized_mir` for available nonlocal function bodies regardless of the requested local-crate `--mir` level. `hax/types/mir.rs:62–69` confirms the same optimized-MIR accessor.
- `translate_bodies.rs:149–157` retrieves a `mir::Body` and immediately passes it to `translate_body`; `translate_bodies.rs:177–204` sets up the operand translation. A narrow diagnostic hook at the `Some(body)` branch, after `get_mir` and before `translate_body`, is the minimal pinned-source insertion point that still holds the rustc `mir::Body` with its operand kinds, places, and `WithRetag` values. This is a proposed observation point only; no hook was added or compiled.
- `get_mir_for_def_id_and_level` has `#[tracing::instrument(skip(tcx))]`, but that records the function call's arguments/result metadata, not a formatted body. Source search found no raw MIR body printer or `--print-mir` option.

`--rustc-arg` is forwarded to rustc (`main.rs:225–245`, `driver.rs:290–303`). A `-Zdump-mir` or `-Zunpretty=mir` flag is only a candidate: the selected method is nonlocal and its body comes from `optimized_mir` loaded from the default sysroot's encoded standard-library MIR. The pinned sources and saved receipt do not establish that such flags would print this already-available dependency body without rebuilding std or adding a diagnostic hook. No flag was tried.

## Existing executable and capture evidence

The pinned cached Charon release executable is `/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon`, 296,187,640 bytes, SHA256 `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`. Its matching source repo is at revision `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`; the queried source files had no tracked working-tree changes. This inventory did not execute Charon, rustc, Cargo, or a build.

R426's captured `--print-original-ullbc` stdout is copied byte-for-byte here as `R426-original-ullbc.stdout`, SHA256 `203ba64981a75e9348e96bdf2920f1905f42c6d756de3c644e60006a440ab412`. The relevant function is at lines 2461 onward; its call appears at line 2498 in this captured text. Full stdout and serialized LLBC remain in the original plan directory. The R426 serialized LLBC SHA256 is `ed43306eac05443a2f4f91121ba8e943a000a66b0d7273eabc40735c64c6f15d`.

## Scope

This is a source/CLI inventory only. It does not authorize a modified Charon build, a new extraction, custom sysroot work, or a semantic repair. It makes no attribution claim about the upstream MIR predecessor of `copy self`.
