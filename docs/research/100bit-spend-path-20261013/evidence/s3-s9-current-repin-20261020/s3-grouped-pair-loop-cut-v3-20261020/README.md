# S3 grouped inactive-pair extracted loop cut (V3)

This packet records a focused Charon/Aeneas extraction of the complete
`s2_grouped_inactive_pair` helper, including all three loop bodies and the
outer calls. The function body and both lookup tables are checked against the
pinned `weights.rs` source. The cut also checks the M31/CM31/QM31/WideExact
field layout and zero/one constants against the pinned current field sources.

The selected Lean `Funs` owner is mechanically adapted from Aeneas output to
remove the `FunsExternal` import (whose generated template contains custom
axioms) and to make add/mul explicit fields of `WideExactOps`. No loop body is
changed. The adapted Types/Funs compile under Lean 4.32.0 with `-M 4400` and
`#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for all
seven generated loop/helper definitions.

This is an operational extracted model, not yet an output-correctness proof.
The caller's decoded coefficient array and the correspondence from explicit
`WideExactOps.add/mul` to the actual current field methods remain boundaries.
The rejected `FunsExternal_Template` is stored under `diagnostics/` only and is
not imported by the selected closure. No OLean or executable is included in
this packet; object hashes and external cache paths are recorded in the
manifest.
