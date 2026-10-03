# R470: current R440 readonly constant graph

Target: `AspisV8R19/R470R440ReadonlyConstantGraph.lean`.

The pinned Lean 4.32 focused build compiled successfully (exit 0) in 1.47 s,
with 2,543,908 KiB peak Lean-child RSS and zero swap.  Source revision was
`f8c3899b2`; the exact target source SHA-256 is
`165e91fbbe31431621d264e453c190ca882a6e23f28dd6e6930ab289f56ddc01`.
The complete log, receipt, saved source, and manifest are in
`evidence/r470-r440-readonly-constant-graph/`.

R470 models the readonly graph present in the current R440 selected callback
capture: QM31 type 2 has captured x86_64 size 16; function 155 is `size_of`,
147 is `SIZE`, and 143 is `IS_ZST`; globals 32 and 31 select those initializers.
It proves the model evaluates global 32 to 16 and global 31 to `false`, and
that replacing the modeled `IS_ZST` scalar read preserves an arbitrary caller
continuation.

All printed declarations use only `propext`, `Classical.choice`, and
`Quot.sound` (or no axioms as shown in the full log).

This does not prove Rust or LLBC execution, layout correctness beyond the
captured row, pointer provenance, the source slice fold, callback chronology,
privacy, or soundness. The first remaining proposition is an actual R440 LLBC
constant-graph correspondence and source-faithful elimination of both captured
`IS_ZST` branches in `Fun70`.
