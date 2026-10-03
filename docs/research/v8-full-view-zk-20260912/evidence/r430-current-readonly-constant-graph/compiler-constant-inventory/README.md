# R430 pinned compiler constant/layout inventory

Read-only source inventory for the exact installed compiler source tree
`/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/rustc-src/rust/compiler`
and Charon checkout
`/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon` (revision
`cb50ff16b9f1066b8a97dc06da704de2da2fa41c`). Full source files are preserved
under `source/`; source file SHA-256 values, upstream paths, line ranges, and
inventory facts are in `inventory.json` and `SHA256SUMS`.

The pinned Rustc CTFE intrinsic handler for `size_of` reads the instantiated
type argument, calls `layout_of`, takes `layout.size.bytes()`, and writes a
`Scalar::from_target_usize` result. Rustc's `Scalar::from_target_usize` uses
the target data layout's `pointer_offset` width. The integer `Eq` branch in
`binary_int_op` converts scalar integers through the operand layouts, then
compares the unsigned `u128` values and returns a boolean scalar. The MIR
builder converts THIR `NamedConst` into a type-system const when
`tcx.is_type_const(def_id)`, otherwise a MIR `Const::Unevaluated`; MIR operand
evaluation reaches `eval_mir_constant`, whose `Const::eval` path sends an
unevaluated MIR const to `tcx.const_eval_resolve`.

Charon's `translate_layout` separately instantiates and normalizes the Rust
type, queries `tcx.layout_of`, and records the sized layout's size and ABI
alignment together with translated discriminator and variant metadata. The
type declaration path attaches that layout under the current target triple.

This bundle records compiler CTFE and type-layout source only. It does not
execute Rustc, run builds, establish a Runtime-pointer or aliasing result, or
prove correspondence between these compiler paths, Aeneas, LLBC, or Lean.
