# Generated `kpowers` P6 success trace

The theorem `kpowers_success_trace` starts from success of the generated
`weights.kpowers` wrapper and derives the ordered callback trace and final
closure/cursor from the pinned P6 array model. It does not assume an arbitrary
array run. Its scope is the generated helper candidate with explicit
`FieldOps`; the callback's field multiplication law and P6-to-Rust
`core::array::from_fn` correspondence remain separate obligations.

Lean 4.32 compiled the focused target with `-j1 -M4400`; exit status was zero,
wall time 3.275 seconds, peak RSS 2,244,460,544 bytes, swap zero. The theorem's
axioms are only `[propext, Classical.choice, Quot.sound]`. No object file is
included.
