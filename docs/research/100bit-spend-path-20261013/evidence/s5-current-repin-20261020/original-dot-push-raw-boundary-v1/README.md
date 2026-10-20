# Original Dot::push extraction with raw boundary

This packet records the unchanged original Rust `canonical::Dot::push` extraction using the pinned alternate Aeneas build. The sole Charon opacity is `canonical::Q::raw`; `Dot::push`, its range loop, and its per-index update body are present in generated `Funs.lean`.

The generated `FunsExternal_Template.lean` contains the expected opaque raw declaration and is retained for provenance only. It is not a clean proof dependency: the next Lean adapter must expose `rawFn` explicitly and must not import the external template. The generated `Funs.lean` also contains Aeneas resource-option directives and is retained as raw generated evidence, not imported as a release owner.

The production `fast_pairing.rs` input is unchanged and pinned by `input/source-pins.json`; the wrapper-only `input/lib.rs` adds the extraction entry point. This packet proves extraction availability only; the original loop-to-four-coordinate Lean refinement remains open.

Aeneas binary: `/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas`, SHA-256 `959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3`.
